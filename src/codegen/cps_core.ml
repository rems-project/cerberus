(* Created by Victor Gomes 2017-03-10 *)

open Util
open Core
open Core_fvs

exception CpsError of string

type basic_expr =
  | CpsPure of typed_pexpr
  | CpsMemop of Mem_common.memop * typed_pexpr list
  | CpsAction of unit typed_paction

type continuation =
  Symbol.sym (* name of the continuation *)
  * Symbol.sym list (* free variables *)
  * typed_pexpr list (* formal parameters *)
  * typed_pexpr option (* return value from previous function, if none then () *)

type control_expr =
  | CpsGoto of (Symbol.sym * Symbol.sym list * typed_pexpr list * typed_pattern option)
  | CpsIf of typed_pexpr * control_expr * control_expr
  | CpsCase of typed_pexpr * (typed_pattern * control_expr) list
  | CpsProc of name * (Symbol.sym * Symbol.sym list) * typed_pexpr list
  | CpsCcall of typed_pexpr * (Symbol.sym * Symbol.sym list) * typed_pexpr list
  | CpsCont of Symbol.sym

let fv_pat_opt = function
  | None -> []
  | Some pat -> fv_pat [] pat

let fv_be fvs = function
  | CpsPure pe -> fv_pe pe fvs
  | CpsMemop (memop, pes) -> List.fold_left (flip fv_pe) fvs pes
  | CpsAction act -> fv_act act fvs

let rec fv_ce ce fvs =
  match ce with
  | CpsGoto (_, fvs2, pes, _) -> List.fold_left (flip fv_pe) (fvs @ fvs2) pes
  | CpsIf (pe1, ce2, ce3) ->
    fv_pe pe1 fvs
    |> fv_ce ce2
    |> fv_ce ce3
  | CpsCase (pe, cases) ->
    List.fold_left (
      fun acc (pat, ce) -> acc@(fvs_rm (fv_pat [] pat) (fv_ce ce []))
    ) [] cases
    |> fv_pe pe
  | CpsCcall (pe, (_, fvs2), pes) ->  List.fold_left (flip fv_pe) (fvs@fvs2) (pe::pes)
  | CpsProc (_, (_, fvs2), pes) ->  List.fold_left (flip fv_pe) (fvs@fvs2) pes
  | CpsCont _ -> fvs

let fv_pat_be (pat_opt, be) fvs =
  fv_be fvs be |> fvs_rm (fv_pat_opt pat_opt)

let fv_cont (pat_opt, ce) =
  fv_ce ce [] |> fvs_rm (fv_pat_opt pat_opt)

(* this is ugly but whatever *)
let label_id = ref 0
let fresh_label () =
  label_id := !label_id + 1;
  Symbol.Symbol (0, Some ("__l" ^ string_of_int !label_id))

module BB =
struct
  type head = Symbol.sym * Symbol.sym list * Symbol.sym list * typed_pattern option
  type body = (typed_pattern option * basic_expr) list
              * (typed_pattern option * control_expr)
  type block =
    BB of head * body

  let fv bes cont =
    List.fold_left (flip fv_pat_be) (fv_cont cont) (List.rev bes)

  let uniq_fv bes cont = fv bes cont |> sort_uniq

  (*
    - add a basic block with expressions es and control expression ce to bbs
    - if es is empty return the previous control expression, otherwise
      build a goto to the created block
  *)
  let add (bbs, (es, (pat2, ce))) =
    match es with
    | [] -> (bbs, pat2, ce)
    | (pat1, be1)::es  ->
      let l = fresh_label() in
      let fvs = uniq_fv ((pat1, be1)::es) (pat2, ce) in
      let bb = BB ((l, fvs, [], pat1), ((None, be1)::es, (pat2, ce))) in
      let goto = CpsGoto (l, fvs, [], pat1) in
      (bb::bbs, pat1, goto)

  let cmp bb1 bb2 =
    match bb1, bb2 with
      BB ((l1, _, _, _), _), BB ((l2, _, _, _), _) -> sym_compare l1 l2
end

let rec cps_transform_expr_left bbs bvs pat1 es pat2 ce e =
  match e with
  | Esseq _ -> raise (CpsError "no assoc")
  | e -> cps_transform_expr bbs bvs pat1 es pat2 ce e
and cps_transform_expr bbs bvs pat1 es pat2 ce e =
  let to_basic e = (bbs, ((pat1, e)::es, (pat2, ce))) in
  match e with
  | Epure pe            -> to_basic (CpsPure pe)
  | Ememop (memop, pes) -> to_basic (CpsMemop (memop, pes))
  | Eaction act         -> to_basic (CpsAction act)
  | Eccall (_, nm, pes) ->
    (match es with
     | [] ->
       let l = fresh_label() in
       let fvs = BB.uniq_fv [] (pat2, ce) in
       let bb = BB.BB ((l, fvs, [], pat2), ([], (pat2, ce))) in
       (bb::bbs, ([], (pat1, CpsCcall (nm, (l, fvs), pes))))
     | (pat1', be1)::es ->
       let l = fresh_label() in
       let fvs = BB.uniq_fv ((pat1', be1)::es) (pat2, ce) in
       let bb = BB.BB ((l, fvs, [], pat1'), ((None, be1)::es, (pat2, ce))) in
    (* TODO: not sure if this is really None or pat1 *)
       (bb::bbs, ([], (pat1, CpsCcall (nm, (l, fvs), pes))))
    )
  | Eproc  (_, nm, pes) ->
    (match es with
     | [] ->
       let l = fresh_label() in
       let fvs = BB.uniq_fv [] (pat2, ce) in
       let bb = BB.BB ((l, fvs, [], pat2), ([], (pat2, ce))) in
       (bb::bbs, ([], (pat1, CpsProc (nm, (l, fvs), pes))))
     | (pat1', be1)::es ->
       let l = fresh_label() in
       let fvs = BB.uniq_fv ((pat1', be1)::es) (pat2, ce) in
       let bb = BB.BB ((l, fvs, [], pat1'), ((None, be1)::es, (pat2, ce))) in
    (* TODO: not sure if this is really None or pat1 *)
       (bb::bbs, ([], (pat1, CpsProc (nm, (l, fvs), pes))))
    )
  | Esave ((sym, _), xs, e) ->
    (* WARN: pat1 is not used, is that normal? *)
    let (bbs, pat', ce') = BB.add (bbs, (es, (pat2, ce))) in
    let (ps, pes) = List.fold_left (
        fun (ls, pes) (l, (_, pe)) -> (l::ls, pe::pes)
      ) ([], []) xs
    in
    let (bbs, bb') = cps_transform_expr bbs bvs None [] pat' ce' e in
    (* TODO FIX: esave can have other free variables other than the parameters
       need to see how I will match with erun *)
    let fvs = (uncurry BB.uniq_fv) bb' |> fvs_rm ps |> fvs_rm bvs in
    let bb = BB.BB ((sym, fvs, ps, None), bb') in
    (bb::bbs, ([], (None, CpsGoto (sym, fvs, pes, None))))
  | Eif (pe1, e2, e3) ->
    let (bbs1, pat', ce') = BB.add (bbs, (es, (pat2, ce))) in
    let (bbs2, pat2', ce2) = BB.add (cps_transform_expr bbs bvs pat1 [] pat' ce' e2) in
    let (bbs3, pat3', ce3) = BB.add (cps_transform_expr bbs bvs pat1 [] pat' ce' e3) in
    (* is pat1 = pat2' = pat3' ? *)
    let cont = (pat1, CpsIf (pe1, ce2, ce3)) in
    (bbs3@bbs2@bbs1, ([], cont))
  | Ecase (pe, cases) ->
    let (bbs, pat', ce') = BB.add (bbs, (es, (pat2, ce))) in
    let (bbs, cases) = List.fold_left (fun (acc, cases) (p, e) ->
        let (bbs, _, ce) = BB.add (cps_transform_expr bbs bvs (Some p) [] pat' ce' e) in
        (bbs@acc, (p, ce)::cases)
      ) (bbs, []) cases
    in
    (bbs, ([], (pat1, CpsCase (pe, cases))))
  | Esseq (pat, e1, e2) ->
    let (bbs2, (es2, (pat', ce'))) = cps_transform_expr bbs bvs (Some pat) es pat2 ce e2 in
    cps_transform_expr_left bbs2 bvs pat1 es2 pat' ce' e1
  | Erun (_, sym, pes) ->
    (bbs, ([], (pat1, CpsGoto (sym, [], List.rev pes, None))))
  | End (e::_) -> cps_transform_expr bbs bvs pat1 es pat2 ce e
  | Eskip ->
    if es != [] then
      raise (CpsError "no skip elim")
    else
      (* eliminate pattern *)
      (bbs, ([], (None, ce))) 
  | Ewseq _  -> raise (CpsError "no only_sseq")
  | End []   -> raise (Unsupported "empty end")
  | Eunseq _ -> raise (Unsupported "unseq")
  | Easeq  _ -> raise (Unsupported "aseq")
  | Eindet _ -> raise (Unsupported "indet")
  | Ebound _ -> raise (Unsupported "bound")
  | Elet   _ -> raise (Unsupported "let")
  | Epar   _ -> raise (Unsupported "par")
  | Ewait  _ -> raise (Unsupported "wait")
  | Eloc   _ -> raise (Unsupported "loc")



type cps_fun =
  | CpsFun of core_base_type * (Symbol.sym * core_base_type) list * typed_pexpr
  | CpsProc of core_base_type * (Symbol.sym * core_base_type) list
              * BB.block list * BB.body

(* return value passed to next continuation *)
(* TODO: should review that *)
let ret_sym = Symbol.Symbol (0, Some "__ret")
let ret_pat = Core.CaseBase (Some ret_sym, Core.BTy_unit)
let ret_pe  = Core.Pexpr (Core.BTy_unit, Core.PEsym ret_sym)
let default = Symbol.Symbol (0, Some "cont")
(*
let cps_transform_expr_main = cps_transform_expr [] None [] (Some ret_pat) (CpsGoto (default, [], [], Some ret_pat))
*)
let cps_transform_expr_main bvs e = cps_transform_expr [] bvs None [] (Some ret_pat) (CpsCont ret_sym) e

let cps_transform_fun = function
  | Fun (bty, params, pe) -> CpsFun (bty, params, pe)
  | Proc (bty, params, e) ->
    let (bbs, bbody) = cps_transform_expr_main (List.map fst params) e
    in
    CpsProc (bty, params, bbs, bbody)


type cps_file = {
  main   : Symbol.sym;
  stdlib : (Symbol.sym, cps_fun) Pmap.map;
  impl   : typed_impl;
  globs  : (Symbol.sym * core_base_type * BB.block list * BB.body) list;
  funs   : (Symbol.sym, cps_fun) Pmap.map;
}


let cps_transform (core : unit typed_file) =
  let globs = List.map (fun (s, bty, e) ->
      let (bbs, bbody) = cps_transform_expr_main [] e
      in
      (s, bty, bbs, bbody)
    ) core.globs
  in
  {
    main = core.main;
    stdlib = Pmap.map cps_transform_fun core.stdlib;
    impl = core.impl;
    globs = globs;
    funs = Pmap.map cps_transform_fun core.funs;
  }

