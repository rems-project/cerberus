open Core

(* ------------------------------------------------------------------ *)
(* Environment: symbol → pexpr map                                    *)
(* ------------------------------------------------------------------ *)

type env = (Symbol.sym, pexpr) Pmap.map

let empty_env : env = Pmap.empty Symbol.compare_sym

let extend_env env alias pe = Pmap.add alias pe env

let extend_env_list env bindings =
  List.fold_left (fun acc (s, pe) -> extend_env acc s pe) env bindings

(* a conservative free-variable and replaceable-with-unit check
 *
 * no free variables because the expression will be substituted (propagated)
 * into other contexts so needs to be well-formed
 *
 * replaceable with unit so that other analyses (like mem2reg) don't
 * see mentions of the propagated value even though it's just rebound
 * to a wildcard pattern
 *
 * cfunction returns a tuple when evaluated so should not be replaced with
 * unit; ccall in practice does not, but could so is also left alone
 *
 * if, let and case could be checked more precisely but not worth the
 * complexity *)

let sym_in binders s =
  List.exists (fun b -> Symbol.compare_sym s b = 0) binders

let rec can_prop_and_rm binders (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s ->
      not (sym_in binders s)
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ ->
      true
  | PEctor (_, pes) ->
      List.for_all (can_prop_and_rm binders) pes
  | PEnot pe1 ->
      can_prop_and_rm binders pe1
  | PEop (_, pe1, pe2)
  | PEwrapI (_, _, pe1, pe2)
  | PEcatch_exceptional_condition (_, _, pe1, pe2)
  | PEare_compatible (pe1, pe2)
  | PEarray_shift (pe1, _, pe2) ->
      can_prop_and_rm binders pe1 && can_prop_and_rm binders pe2
  | PEmemberof (_, _, pe1)
  | PEmember_shift (pe1, _, _)
  | PEconv_int (_, pe1)
  | PEis_scalar pe1 | PEis_integer pe1
  | PEis_signed pe1 | PEis_unsigned pe1
  | PEbmc_assume pe1
  | PEunion (_, _, pe1) ->
      can_prop_and_rm binders pe1
  | PEmemop (_, pes) ->
      List.for_all (can_prop_and_rm binders) pes
  | PEstruct (_, fields) ->
      List.for_all (fun (_, pe1) -> can_prop_and_rm binders pe1) fields
  | PEif _ | PElet _ | PEcase _ | PEconstrained _ ->
      false  (* not worth extra complexity *)
   | PEcall _ | PEcfunction _ ->
     false (* unsafe to replace with unit *)

let rec binders_of_pat (Pattern (_, pat_)) =
  match pat_ with
  | CaseBase (None, _)   -> []
  | CaseBase (Some s, _) -> [s]
  | CaseCtor (_, pats)   -> List.concat_map binders_of_pat pats

let prop_and_rm binders pe =
  let ret_pe ~new_ ~old:(Pexpr (annot, a, _)) = Pexpr (annot, a, new_) in
  let unit_pe = ret_pe ~new_:(PEval Vunit) ~old:pe in
  let (tail, pe) =
    if can_prop_and_rm binders pe then
      (Some pe, unit_pe)
    else
      (None, pe) in
  (tail, pe)

(* ------------------------------------------------------------------ *)
(* pexpr_tree: rose tree of pexpr option mirroring Eunseq structure  *)
(*                                                                    *)
(* Leaf(Some pe) — this position has a known, safe-to-hoist pexpr.  *)
(* Leaf None     — this position is opaque (action, unsafe, etc.).   *)
(* Node ts       — this position is an Eunseq with children ts.      *)
(* ------------------------------------------------------------------ *)

type pexpr_tree =
  | Leaf of pexpr option
  | Node of pexpr_tree list

(* this is important to allow for fine-grained copy-prop inside
 * elements of a tuple *)
let rec split_tuple binders = function
  | Pexpr (annot, ty, PEctor (Ctuple, pes)) ->
    let (tails, pes') = List.split @@ List.map (split_tuple binders) pes in
    (Node tails, Pexpr (annot, ty, PEctor (Ctuple, pes')))
  | pe ->
    let (tail, pe) = prop_and_rm binders pe in
    (Leaf tail, pe)

(* A common pattern in elaborated Core is something like
 * let pat = e1 in let pat e2 in .. pure(pe) or
 * let pat = e1 in let pat e2 in .. unseq(pure(pe), ..)
 * i.e. chains of bindings that eventually end in a pure value,
 * which can be removed (replaced with a unit), and propagated
 * under the conditions of can_prop_and_rm
 *
 * Hence, this function constructs the tuple-nesting structure,
 * used later to match against nested tuple pattern matches,
 * and also returns the expression but with the pure value
 * replaced with a unit *)
let rec eventually_pure binders (Expr (annot, e_)) =
  let ret_e e_ = (Expr (annot, e_)) in
  match e_ with
  | Epure pe ->
    let (tail, pe) = split_tuple binders pe in
    (tail, ret_e (Epure pe))
  | Eunseq es ->
    let (tails, es') = List.split @@ List.map (eventually_pure binders) es in
    (Node tails, ret_e (Eunseq es'))
  | Ewseq (pat, e1, e2) ->
    let (tail, e2) = eventually_pure (binders_of_pat pat @ binders) e2 in
    (tail, ret_e (Ewseq (pat, e1, e2)))
  | Esseq (pat, e1, e2) ->
    let (tail, e2) = eventually_pure (binders_of_pat pat @ binders) e2 in
    (tail, ret_e (Esseq (pat, e1, e2)))
  | Elet (pat, pe1, e2) ->
    let (tail, e2) = eventually_pure (binders_of_pat pat @ binders) e2 in
    (tail, ret_e (Elet (pat, pe1, e2)))
  | Ebound e ->
      let (tail, e) = eventually_pure binders e in
      (tail, ret_e (Ebound e))
  | Eannot (al, e) ->
      let (tail, e) = eventually_pure binders e in
      (tail, ret_e (Eannot (al, e)))
  | _ ->
      (Leaf None, ret_e e_)

let tail_pexpr e = eventually_pure [] e

(* ------------------------------------------------------------------ *)
(* match_pat_tree: extract bindings by walking pattern and tree       *)
(*                                                                    *)
(* Returns (bindings, new_pattern) where:                             *)
(*   bindings    — (sym, pexpr) pairs for extractable positions       *)
(*   new_pattern — pattern with extracted positions as wildcard units *)
(*                                                                    *)
(* Partial: positions where the tree has Leaf None are left named.    *)
(* ------------------------------------------------------------------ *)

let rec match_pat_tree pat tree =
  match pat, tree with

  | Pattern (p_annots, CaseBase (Some s, cbty)), Leaf (Some pe) ->
      ([(s, pe)], Pattern (p_annots, CaseBase (None, BTy_unit)))

  | Pattern (p_annots, CaseBase (None, _)), Leaf (Some _) ->
      ([], Pattern (p_annots, CaseBase (None, BTy_unit)))

  (* Tuple pattern vs a matching-arity Node (Eunseq): recurse element-wise *)
  | Pattern (p_annots, CaseCtor (Ctuple, pats)), Node trees ->
    (* they should have the same length otherwise there's a bug in the tree
     * construction or the elaboration *)
    let results = List.map2 match_pat_tree pats trees in
    let bindings = List.concat_map fst results in
    let new_pats = List.map snd results in
    (bindings, Pattern (p_annots, CaseCtor (Ctuple, new_pats)))

  | _ ->
      ([], pat)

(* ------------------------------------------------------------------ *)
(* Mutually recursive propagation functions.                          *)
(*                                                                    *)
(* propagate_pexpr, propagate_action, propagate_expr thread an env   *)
(* (alias → pexpr) through the Core IR in a single top-down pass,   *)
(* rewriting PEsym occurrences and dropping trivial bindings.        *)
(* ------------------------------------------------------------------ *)

let rec propagate_pexpr env (Pexpr (annots, bty, pe_) as pe) =
  match pe_ with
  | PEsym s ->
      (match Pmap.lookup s env with
       | Some pe' -> pe'
       | None     -> Pexpr (annots, bty, PEsym s))
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ | PEconstrained _ ->
      pe
  | PElet (pat, pe1, pe2) ->
      let pe1' = propagate_pexpr env pe1 in
      let (tail, pe1') = split_tuple [] pe1' in
      let (bindings, new_pat) = match_pat_tree pat tail in
      let env' = extend_env_list env bindings in
      Pexpr (annots, bty, PElet (new_pat, pe1', propagate_pexpr env' pe2))
  | PEctor (c, pes) ->
      Pexpr (annots, bty, PEctor (c, List.map (propagate_pexpr env) pes))
  | PEcase (pe1, arms) ->
      Pexpr (annots, bty, PEcase (propagate_pexpr env pe1,
        List.map (fun (pat, pe2) -> (pat, propagate_pexpr env pe2)) arms))
  | PEarray_shift (pe1, cty, pe2) ->
      Pexpr (annots, bty,
        PEarray_shift (propagate_pexpr env pe1, cty, propagate_pexpr env pe2))
  | PEmember_shift (pe1, sym, id) ->
      Pexpr (annots, bty, PEmember_shift (propagate_pexpr env pe1, sym, id))
  | PEmemop (op, pes) ->
      Pexpr (annots, bty, PEmemop (op, List.map (propagate_pexpr env) pes))
  | PEnot pe1 ->
      Pexpr (annots, bty, PEnot (propagate_pexpr env pe1))
  | PEop (op, pe1, pe2) ->
      Pexpr (annots, bty,
        PEop (op, propagate_pexpr env pe1, propagate_pexpr env pe2))
  | PEconv_int (ity, pe1) ->
      Pexpr (annots, bty, PEconv_int (ity, propagate_pexpr env pe1))
  | PEwrapI (ity, iop, pe1, pe2) ->
      Pexpr (annots, bty,
        PEwrapI (ity, iop, propagate_pexpr env pe1, propagate_pexpr env pe2))
  | PEcatch_exceptional_condition (ity, iop, pe1, pe2) ->
      Pexpr (annots, bty,
        PEcatch_exceptional_condition (ity, iop,
          propagate_pexpr env pe1,
          propagate_pexpr env pe2))
  | PEstruct (sym, fields) ->
      Pexpr (annots, bty,
        PEstruct (sym,
          List.map (fun (id, pe1) -> (id, propagate_pexpr env pe1)) fields))
  | PEunion (sym, id, pe1) ->
      Pexpr (annots, bty, PEunion (sym, id, propagate_pexpr env pe1))
  | PEcfunction pe1 ->
      Pexpr (annots, bty, PEcfunction (propagate_pexpr env pe1))
  | PEmemberof (sym, id, pe1) ->
      Pexpr (annots, bty, PEmemberof (sym, id, propagate_pexpr env pe1))
  | PEcall (name, pes) ->
      Pexpr (annots, bty, PEcall (name, List.map (propagate_pexpr env) pes))
  | PEif (pe1, pe2, pe3) ->
      Pexpr (annots, bty, PEif (
        propagate_pexpr env pe1,
        propagate_pexpr env pe2,
        propagate_pexpr env pe3))
  | PEis_scalar pe1 ->
      Pexpr (annots, bty, PEis_scalar (propagate_pexpr env pe1))
  | PEis_integer pe1 ->
      Pexpr (annots, bty, PEis_integer (propagate_pexpr env pe1))
  | PEis_signed pe1 ->
      Pexpr (annots, bty, PEis_signed (propagate_pexpr env pe1))
  | PEis_unsigned pe1 ->
      Pexpr (annots, bty, PEis_unsigned (propagate_pexpr env pe1))
  | PEbmc_assume pe1 ->
      Pexpr (annots, bty, PEbmc_assume (propagate_pexpr env pe1))
  | PEare_compatible (pe1, pe2) ->
      Pexpr (annots, bty,
        PEare_compatible (propagate_pexpr env pe1, propagate_pexpr env pe2))

(* Propagate env into all pexprs inside an action. *)
let propagate_action env (Paction (pol, Action (loc, a, act_))) =
  let pp = propagate_pexpr env in
  let act_' = match act_ with
    | Create (pe1, pe2, prefix) ->
        Create (pp pe1, pp pe2, prefix)
    | CreateReadOnly (pe1, pe2, pe3, prefix) ->
        CreateReadOnly (pp pe1, pp pe2, pp pe3, prefix)
    | Alloc0 (pe1, pe2, prefix) ->
        Alloc0 (pp pe1, pp pe2, prefix)
    | Kill (kind, pe1) ->
        Kill (kind, pp pe1)
    | Store0 (lk, pe1, pe2, pe3, mo) ->
        Store0 (lk, pp pe1, pp pe2, pp pe3, mo)
    | Load0 (pe1, pe2, mo) ->
        Load0 (pp pe1, pp pe2, mo)
    | SeqRMW (lk, pe1, pe2, sym, pe3) ->
        SeqRMW (lk, pp pe1, pp pe2, sym, pp pe3)
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        RMW0 (pp pe1, pp pe2, pp pe3, pp pe4, mo1, mo2)
    | Fence0 mo ->
        Fence0 mo
    | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
        CompareExchangeStrong (pp pe1, pp pe2, pp pe3, pp pe4, mo1, mo2)
    | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
        CompareExchangeWeak (pp pe1, pp pe2, pp pe3, pp pe4, mo1, mo2)
    | LinuxFence mo ->
        LinuxFence mo
    | LinuxLoad (pe1, pe2, mo) ->
        LinuxLoad (pp pe1, pp pe2, mo)
    | LinuxStore (pe1, pe2, pe3, mo) ->
        LinuxStore (pp pe1, pp pe2, pp pe3, mo)
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        LinuxRMW (pp pe1, pp pe2, pp pe3, mo)
  in
  Paction (pol, Action (loc, a, act_'))

(* Single top-down pass threading the env through exprs *)
let rec propagate_expr env (Expr (annots, e_) as expr) =
  let pp = propagate_pexpr env in
  let pe = propagate_expr  env in
  match e_ with
  | Ewseq (pat, e1, body) ->
      let e1' = propagate_expr env e1 in
      let (tail, e1') = tail_pexpr e1' in
      let (bindings, new_pat) = match_pat_tree pat tail in
      let env' = extend_env_list env bindings in
      Expr (annots, Ewseq (new_pat, e1', propagate_expr env' body))

  | Esseq (pat, e1, body) ->
      let e1' = propagate_expr env e1 in
      let (tail, e1') = tail_pexpr e1' in
      let (bindings, new_pat) = match_pat_tree pat tail in
      let env' = extend_env_list env bindings in
      Expr (annots, Esseq (new_pat, e1', propagate_expr env' body))

  | Elet (pat, pe1, body) ->
      let pe1' = propagate_pexpr env pe1 in
      let (tail, pe1') = split_tuple [] pe1' in
      let (bindings, new_pat) = match_pat_tree pat tail in
      let env' = extend_env_list env bindings in
      Expr (annots, Elet (new_pat, pe1', propagate_expr env' body))

  (* ---- Other expression forms: recurse ---- *)
  | Epure pe1 ->
      Expr (annots, Epure (pp pe1))
  | Ememop (op, pes) ->
      Expr (annots, Ememop (op, List.map pp pes))
  | Eaction pact ->
      Expr (annots, Eaction (propagate_action env pact))
  | Ecase (pe1, arms) ->
      Expr (annots, Ecase (pp pe1,
        List.map (fun (pat, e2) -> (pat, pe e2)) arms))
  | Eif (pe1, e1, e2) ->
      Expr (annots, Eif (pp pe1, pe e1, pe e2))
  | Eccall (a, pe1, pe2, pes) ->
      Expr (annots, Eccall (a, pp pe1, pp pe2, List.map pp pes))
  | Eproc (a, name, pes) ->
      Expr (annots, Eproc (a, name, List.map pp pes))
  | Eunseq es ->
      Expr (annots, Eunseq (List.map pe es))
  | Esave (sym_bty, args, body) ->
      Expr (annots, Esave (sym_bty,
        List.map (fun (s, (type_info, pe1)) -> (s, (type_info, pp pe1))) args,
        pe body))
  | Erun (a, lbl, pes) ->
      Expr (annots, Erun (a, lbl, List.map pp pes))
  | Ebound e ->
      Expr (annots, Ebound (pe e))
  | Eannot (fps, e) ->
      Expr (annots, Eannot (fps, pe e))
  | End es ->
      Expr (annots, End (List.map pe es))
  | Epar es ->
      Expr (annots, Epar (List.map pe es))
  | Ewait _ ->
      expr
  | Eexcluded _ ->
      expr

(* ------------------------------------------------------------------ *)
(* Top-level file transform                                           *)
(* ------------------------------------------------------------------ *)

let transform_file file =
  let pr e  = propagate_expr  empty_env e in
  let pp pe = propagate_pexpr empty_env pe in
  let rewrite_impl_decl = function
    | Def (bty, pe)        -> Def (bty, pp pe)
    | IFun (bty, args, pe) -> IFun (bty, args, pp pe) in
  let rewrite_fun_map_decl = function
    | Fun (bty, args, pe)            -> Fun (bty, args, pp pe)
    | Proc (loc, mrk, bty, args, e, promotable) -> Proc (loc, mrk, bty, args, pr e, promotable)
    | decl                           -> decl in
  let rewrite_globs = function
    | GlobalDef (bty_cty, e) -> GlobalDef (bty_cty, pr e)
    | decl                   -> decl in
  { file with
    stdlib = Pmap.map rewrite_fun_map_decl file.stdlib
  ; impl   = Pmap.map rewrite_impl_decl   file.impl
  ; globs  = List.map (fun (sym, g) -> (sym, rewrite_globs g)) file.globs
  ; funs   = Pmap.map rewrite_fun_map_decl file.funs }
