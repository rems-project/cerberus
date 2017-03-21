(* Created by Victor Gomes 2017-03-10 *)

open Util
open Core
open Core_fvs

exception CpsError of string

type basic_expr =
  | CpsPure of typed_pexpr
  | CpsMemop of Mem_common.memop * typed_pexpr list
  | CpsAction of unit typed_paction
  | CpsCcall of typed_pexpr * typed_pexpr list
  | CpsProc of name * typed_pexpr list

type continuation =
  Symbol.sym (* name of the continuation *)
  * Symbol.sym list (* free variables *)
  * typed_pexpr list (* formal parameters *)
  * typed_pexpr option (* return value from previous function, if none then () *)

type control_expr =
  | CpsGoto of (Symbol.sym * Symbol.sym list * typed_pexpr list * typed_pattern option)
  | CpsIf of typed_pexpr * control_expr * control_expr
  | CpsCase of typed_pexpr * (typed_pattern * control_expr) list

let fv_pat_opt = function
  | None -> []
  | Some pat -> fv_pat [] pat

let fv_be fvs = function
  | CpsPure pe -> fv_pe pe fvs
  | CpsMemop (memop, pes) -> List.fold_left (flip fv_pe) fvs pes
  | CpsAction act -> fv_act act fvs
  | CpsCcall (pe, pes) ->  List.fold_left (flip fv_pe) fvs (pe::pes)
  | CpsProc (_, pes) ->  List.fold_left (flip fv_pe) (fvs) pes

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

  let create es (pato, ce) =
    let l = fresh_label() in
    let fvs = uniq_fv es (pato, ce)
(*
      match es with
      | [] -> sort_uniq (uniq_fv es (pato, ce)
            @ (match pato with None -> [] | Some pat -> fv_pat [] pat))
      | _  -> uniq_fv es (pato, ce)*)
    in BB ((l, fvs, [], pato), (es, (pato, ce)))

  let goto ret = function
      BB ((l, fvs, _, _), (_, (pato, _))) ->
      (*let pe = List.map (fun s -> Pexpr (BTy_unit, PEsym s)) fvs in*)
      CpsGoto (l, fvs, [], ret)

  (*
    - add a basic block with expressions es and control expression ce to bbs
    - if es is empty return the previous control expression, otherwise
      build a goto to the created block
  *)
  let add ret_pat (bbs, (es, (pato, ce))) =
    match es with
    | [] -> (bbs, (pato, ce))
    | (_, be)::es  ->
      let bb = create ((ret_pat, be)::es) (pato, ce) in
      (bb::bbs, (pato, goto ret_pat bb))

  let cmp bb1 bb2 =
    match bb1, bb2 with
      BB ((l1, _, _, _), _), BB ((l2, _, _, _), _) -> sym_compare l1 l2
end

let rec cps_transform_expr_left bbs es pato cont e =
  match e with
  | Esseq _ -> raise (CpsError "no assoc")
  | e -> cps_transform_expr bbs es pato cont e
and cps_transform_expr bbs es pato cont e =
  let to_basic e = (bbs, ((pato, e)::es, cont)) in
  match e with
  | Epure pe            -> to_basic (CpsPure pe)
  | Ememop (memop, pes) -> to_basic (CpsMemop (memop, pes))
  | Eaction act         -> to_basic (CpsAction act)
  | Eccall (_, nm, pes) -> to_basic (CpsCcall (nm, pes))
  | Eproc  (_, nm, pes) -> to_basic (CpsProc (nm, pes))
  | Esave ((sym, _), xs, e) ->
    let (bbs, cont) = BB.add pato (bbs, (es, cont)) in
    let (ps, pes) = List.fold_left (
        fun (ls, pes) (l, (_, pe)) -> (l::ls, pe::pes)
      ) ([], []) xs
    in
    let (bbs, bb') = cps_transform_expr bbs [] None cont e in
    (* TODO FIX: esave can have other free variables other than the parameters
       need to see how I will match with erun *)
    let fvs = (uncurry BB.uniq_fv) bb' |> fvs_rm ps in
    (*let fvs_pes = List.map (fun s -> Pexpr (BTy_unit, PEsym s)) fvs in *)
    let bb = BB.BB ((sym, fvs, ps, pato), bb') in
    (bb::bbs, ([], (pato, CpsGoto (sym, fvs, pes, pato))))
  | Eif (pe1, e2, e3) ->
    let (bbs1, cont) = BB.add pato (bbs, (es, cont)) in
    let (bbs2, (_, ce2)) = BB.add pato (cps_transform_expr bbs [] None cont e2) in
    let (bbs3, (_, ce3)) = BB.add pato (cps_transform_expr bbs [] None cont e3) in
    let cont = (pato, CpsIf (pe1, ce2, ce3)) in
    (bbs3@bbs2@bbs1, (es, cont))
  | Ecase (pe, cases) ->
    let (bbs, cont) = BB.add pato (bbs, (es, cont)) in
    let (bbs, cases) = List.fold_left (fun (acc, cases) (p, e) ->
        let (bbs, (_, ce)) = BB.add pato (cps_transform_expr bbs [] None cont e) in
        (bbs@acc, (p, ce)::cases)
      ) (bbs, []) cases
    in
    (bbs, ([], (pato, CpsCase (pe, cases))))
  | Esseq (pat, e1, e2) ->
    let (bbs2, (es2, cont2)) = cps_transform_expr bbs es (Some pat) cont e2 in
    cps_transform_expr_left bbs2 es2 pato cont2 e1
  | Erun (_, sym, pes) ->
    (bbs, ([], (pato, CpsGoto (sym, [], List.rev pes, pato))))
  | End (e::_) -> cps_transform_expr bbs es pato cont e
  | Eskip ->
    if es != [] then
      raise (CpsError "no skip elim")
    else
      (* eliminate pattern *)
      (bbs, ([], (match cont with (_, jmp) -> (None, jmp))))
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

let cps_transform_fun = function
  | Fun (bty, params, pe) -> CpsFun (bty, params, pe)
  | Proc (bty, params, e) ->
    let (bbs, bbody) = cps_transform_expr [] [] None
        (Some ret_pat, CpsGoto (default, [ret_sym], [], Some ret_pat)) e
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
      let (bbs, bbody) = cps_transform_expr [] [] None
          (Some ret_pat, CpsGoto (default, [ret_sym], [], None)) e
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

