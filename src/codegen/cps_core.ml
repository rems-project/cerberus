(* Created by Victor Gomes 2017-03-10 *)

open Util
open Core
open Core_fvs

exception CpsError of string

(* AST definitions *)

let (@) xs ys = List.rev (List.rev_append xs ys)

type basic_expr =
  | CpsPure of typed_pexpr
  | CpsMemop of Mem_common.memop * typed_pexpr list
  | CpsAction of unit typed_paction

type control_expr =
  | CpsGoto of (Symbol.sym * typed_pexpr list * typed_pattern option)
  | CpsProc of name * (Symbol.sym * Symbol.sym list) * typed_pexpr list
  | CpsCcall of typed_pexpr * (Symbol.sym * Symbol.sym list) * typed_pexpr list
  | CpsCont of Symbol.sym
  | CpsIf of typed_pexpr * control_expr * control_expr
  | CpsCase of typed_pexpr * (typed_pattern * control_expr) list
  | CpsNd of control_expr list

(* basic blocks *)
type block_head = Symbol.sym * Symbol.sym list * typed_pattern option
type block_body = (typed_pattern option * basic_expr) list
                  * (typed_pattern option * control_expr)
type block =
    BB of block_head * block_body

(* Free Variables *)
let fv_be fvs = function
  | CpsPure pe -> fv_pe pe fvs
  | CpsMemop (memop, pes) -> List.fold_left (flip fv_pe) fvs pes
  | CpsAction act -> fv_act act fvs

let rec fv_ce ce fvs =
  match ce with
  | CpsGoto (_, pes, _) -> List.fold_left (flip fv_pe) fvs pes
  | CpsIf (pe1, ce2, ce3) ->
    fv_pe pe1 fvs
    |> fv_ce ce2
    |> fv_ce ce3
  | CpsCase (pe, cases) ->
    List.fold_left (
      fun acc (pat, ce) -> acc@(fvs_rm (fv_pat [] pat) (fv_ce ce []))
    ) [] cases
    |> fv_pe pe
  | CpsCcall (pe, (_, fvs'), pes) ->
    List.fold_left (flip fv_pe) (fvs@fvs') (pe::pes)
  | CpsProc (_, (_, fvs'), pes) ->
    List.fold_left (flip fv_pe) (fvs@fvs') pes
  | CpsCont _ -> fvs
  | CpsNd xs -> List.fold_left (flip fv_ce) fvs xs

let fv_pat_be (pat_opt, be) fvs =
  fv_be fvs be |> fvs_rm (fv_pat_opt pat_opt)

let fv_cont (pat_opt, ce) =
  fv_ce ce [] |> fvs_rm (fv_pat_opt pat_opt)

let uniq_fv globs bes cont =
  let fv bes cont =
    List.fold_left (flip fv_pat_be) (fv_cont cont) (List.rev bes)
  in fv bes cont |> fvs_rm globs |> sort_uniq

(* TODO: this is ugly but whatever *)
let label_id = ref 0
let fresh_label () =
  label_id := !label_id + 1;
  Symbol.Symbol (0, Some ("__l" ^ string_of_int !label_id))

(* TODO: correctly type this *)
let pexpr_of_sym sym = Pexpr ([], BTy_unit, PEsym sym)

(* Helper functions *)

let block_goto globs (bbs, (es, (pat2, ce))) =
  match es with
  | [] -> (bbs, pat2, ce)
  | (pat1, be1)::es  ->
    let l = fresh_label() in
    let fvs = uniq_fv globs ((pat1, be1)::es) (pat2, ce) in
    let bb = BB ((l, fvs, pat1), ((None, be1)::es, (pat2, ce))) in
    let goto = CpsGoto (l, List.map pexpr_of_sym fvs, pat1) in
    (bb::bbs, pat1, goto)

let block_call es pat2 ce =
  let l = fresh_label() in
  let fvs = uniq_fv [] es (pat2, ce) in
  match es with
  | [] ->
    let bb = BB ((l, fvs, pat2), ([], (pat2, ce))) in
    (bb, (l, fvs))
  | (pat1, be1)::es2 ->
    let bb = BB ((l, fvs, pat1), ((None, be1)::es2, (pat2, ce))) in
    (bb, (l, fvs))

let block_compare (BB ((l1, _, _), _)) (BB ((l2, _, _), _)) = sym_compare l1 l2

(* TODO: should review that *)
let default = Symbol.Symbol (0, Some "cont")

(* CPS transformation *)

(* Transform Core in CPS Core using sym_supply to create new symbols *)
(* TODO: do I need the bound variable lists (bvs) ? *)
let cps_transform_expr sym_supply globs bvs core_expr =
  (* Transform the left hand side of an esseq *)
  (* INVARIANT: we consider that Core is associated to the right, so we cannot
   * find any esseq here! *)
  (* TODO: I might be able to relax this invariant *)
  let rec tr_left bbs pat1 es pat2 ce (Expr (_, e_) as e) =
    match e_ with
    | Esseq _ -> raise (Unexpected "Sequencing must be associate to the right!")
    | _ -> tr_right bbs pat1 es pat2 ce e
  (* Transform from right to left (esseq), bottom to top from a Core expression *)
  (* bbs is an accumulated list of blocks (will become functions)
   * pat1 is the pattern to enter the current basic block
   * es  is an accumulated list of basic blocks (actions, will become a basic block)
   * pat2 is the pattern to leave the current basic block (return value)
   * ce the control jump from the current basic block (continuation)
   * (pat1 - es - pat2 - ce) form the current basic block being created *)
  and tr_right bbs pat1 es pat2 ce (Expr (_, e_)) =
    let to_basic e = (bbs, ((pat1, e)::es, (pat2, ce))) in
    match e_ with
    | Epure pe            -> to_basic (CpsPure pe)
    | Ememop (memop, pes) -> to_basic (CpsMemop (memop, pes))
    | Eaction act         -> to_basic (CpsAction act)
    | Eccall (_, _, nm, pes) ->
      let (bb, args) = block_call es pat2 ce in
      (bb::bbs, ([], (pat1, CpsCcall (nm, args, pes))))
    | Eproc  (_, nm, pes) ->
      let (bb, args) = block_call es pat2 ce in
      (bb::bbs, ([], (pat1, CpsProc (nm, args, pes))))
    | Esave ((sym, _), xs, e) ->
      (* WARN: pat1 is not used, is that normal? *)
      let (bbs, pat', ce') = block_goto globs (bbs, (es, (pat2, ce))) in
      let (ps, pes) = List.fold_left (
          fun (ls, pes) (l, (_, pe)) -> (l::ls, pe::pes)
        ) ([], []) xs
      in
      let (bbs, bb') = tr_right bbs None [] pat' ce' e in
      let bb = BB ((sym, ps, None), bb') in
      (bb::bbs, ([], (None, CpsGoto (sym, pes, None))))
    | Eif (pe1, e2, e3) ->
      let (bbs1, pat', ce') = block_goto globs (bbs, (es, (pat2, ce))) in
      let (bbs2, _, ce2) = block_goto globs (tr_right bbs1 pat1 [] pat' ce' e2) in
      let (bbs3, _, ce3) = block_goto globs (tr_right bbs2 pat1 [] pat' ce' e3) in
      (* is pat1 = pat2' = pat3' ? *)
      let cont = (pat1, CpsIf (pe1, ce2, ce3)) in
      (bbs3, ([], cont))
    | Ecase (pe, cases) ->
      let (bbs, pat', ce') = block_goto globs (bbs, (es, (pat2, ce))) in
      let (bbs, cases) = List.fold_left (fun (acc, cases) (p, e) ->
          let (bbs, _, ce) =
            block_goto globs (tr_right acc (Some p) [] pat' ce' e)
          in (bbs, (p, ce)::cases)
        ) (bbs, []) cases
      in
      (bbs, ([], (pat1, CpsCase (pe, cases))))
    | Esseq (pat, e1, e2) ->
      let (bbs2, (es2, (pat', ce'))) = tr_right bbs (Some pat) es pat2 ce e2 in
      tr_left bbs2 pat1 es2 pat' ce' e1
    | Erun (_, sym, pes) ->
      (bbs, ([], (pat1, CpsGoto (sym, List.rev pes, None))))
    | End []   -> raise (Unsupported "empty nd")
    | End nds ->
      let (bbs, pat', ce') = block_goto globs (bbs, (es, (pat2, ce))) in
      let (bbs, ces) = List.fold_left (fun (acc, ces) e ->
          let (bbs, _, ce) = block_goto globs (tr_right acc pat1 [] pat' ce' e)
          in (bbs, ce::ces)
        ) (bbs, []) nds
      in
      (bbs, ([], (pat1, CpsNd ces)))
    | Eskip ->
      if es != [] then
        raise (Unexpected "Skip expression not allowed.")
      else
        to_basic (CpsPure (Pexpr ([], BTy_unit, PEval Vunit)))
    | Ebound (_, e) ->
      (* WARN: I am not sure if this is the correct semantics of Ebound *)
      tr_right bbs pat1 es pat2 ce e
    | Ewseq _  -> raise (Unexpected "Weak sequencing expression not allowed.")
    | Eunseq _ -> raise (Unsupported "Unsequencing operations not supported.")
    | Easeq  _ -> raise (Unexpected "Atomic sequencing must be eliminated.")
    | Eindet _ -> raise (Unsupported "elim indet")
    | Elet   _ -> raise (Unsupported "Let expressions must be eliminated.")
    | Epar   _ -> raise (Unsupported "Concurrent operation `par` not supported.")
    | Ewait  _ -> raise (Unsupported "Concurrent operation `wait` not supported.")
  in
  let (ret_sym, _) = Symbol.fresh sym_supply in
  (* TODO: type check/annotate this symbol *)
  let ret_pat = Core.Pattern ([], Core.CaseBase (Some ret_sym, Core.BTy_unit)) in
  tr_right [] None [] (Some ret_pat) (CpsCont ret_sym) core_expr


type cps_fun =
  | CpsFun of core_base_type * (Symbol.sym * core_base_type) list * typed_pexpr
  | CpsProc of core_base_type * (Symbol.sym * core_base_type) list
              * block list * block_body

let cps_transform_fun sym_supply globs = function
  | Fun (bty, params, pe) -> CpsFun (bty, params, pe)
  | Proc (_, bty, params, e) ->
    let (bbs, bbody) =
      cps_transform_expr sym_supply globs (List.map fst params) e
    in CpsProc (bty, params, bbs, bbody)
  | ProcDecl _ -> raise (Unsupported "Procedures declaration should be eliminated.")
  | BuiltinDecl _ -> raise (Unsupported "Builtin procedures declaration should be eliminated.")

type cps_file = {
  main   : Symbol.sym option;
  stdlib : (Symbol.sym, cps_fun) Pmap.map;
  impl   : typed_impl;
  globs  : (Symbol.sym * core_base_type * block list * block_body) list;
  funs   : (Symbol.sym, cps_fun) Pmap.map;
}

let cps_transform sym_supply globs_sym (core : unit typed_file) =
  let globs = List.map (fun (s, bty, e) ->
      let (bbs, bbody) = cps_transform_expr sym_supply globs_sym [] e in
      (s, bty, bbs, bbody)
    ) core.globs
  in
  (* Add struct/union members to global symbols *)
  let globs_sym' =
    try
      let tags = Tags.tagDefs () in
      globs_sym @ Pset.elements (Pmap.domain tags)
    with _ -> globs_sym
  in
  {
    main = core.main;
    stdlib = Pmap.map (cps_transform_fun sym_supply globs_sym') core.stdlib;
    impl = core.impl;
    globs = globs;
    funs = Pmap.map (cps_transform_fun sym_supply globs_sym') core.funs;
  }

