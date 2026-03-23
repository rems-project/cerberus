open Core

(* ------------------------------------------------------------------ *)
(* Environment: symbol → pexpr map                                    *)
(* ------------------------------------------------------------------ *)

type env = (Symbol.sym, pexpr) Pmap.map

let empty_env : env = Pmap.empty Symbol.compare_sym

let extend_env env alias pe = Pmap.add alias pe env

(* ------------------------------------------------------------------ *)
(* pexpr_safe: conservative free-variable check                       *)
(*                                                                    *)
(* Returns [true] when none of [pe]'s free symbols appear in         *)
(* [binders].  Complex forms (PEif, PElet, PEcase, PEconstrained)    *)
(* return [false] conservatively to avoid a full free-variable        *)
(* analysis.                                                          *)
(* ------------------------------------------------------------------ *)

let sym_in binders s =
  List.exists (fun b -> Symbol.compare_sym s b = 0) binders

let rec pexpr_safe binders (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s ->
      not (sym_in binders s)
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ ->
      true
  | PEctor (_, pes) ->
      List.for_all (pexpr_safe binders) pes
  | PEnot pe1 ->
      pexpr_safe binders pe1
  | PEop (_, pe1, pe2)
  | PEwrapI (_, _, pe1, pe2)
  | PEcatch_exceptional_condition (_, _, pe1, pe2)
  | PEare_compatible (pe1, pe2)
  | PEarray_shift (pe1, _, pe2) ->
      pexpr_safe binders pe1 && pexpr_safe binders pe2
  | PEmemberof (_, _, pe1)
  | PEmember_shift (pe1, _, _)
  | PEconv_int (_, pe1)
  | PEis_scalar pe1 | PEis_integer pe1
  | PEis_signed pe1 | PEis_unsigned pe1
  | PEbmc_assume pe1 | PEcfunction pe1
  | PEunion (_, _, pe1) ->
      pexpr_safe binders pe1
  | PEmemop (_, pes) | PEcall (_, pes) ->
      List.for_all (pexpr_safe binders) pes
  | PEstruct (_, fields) ->
      List.for_all (fun (_, pe1) -> pexpr_safe binders pe1) fields
  | PEif _ | PElet _ | PEcase _ | PEconstrained _ ->
      false  (* conservative *)

(* ------------------------------------------------------------------ *)
(* binders_of_pat: collect all named symbols in a pattern             *)
(* ------------------------------------------------------------------ *)

let rec binders_of_pat (Pattern (_, pat_)) =
  match pat_ with
  | CaseBase (None, _)   -> []
  | CaseBase (Some s, _) -> [s]
  | CaseCtor (_, pats)   -> List.concat_map binders_of_pat pats

(* ------------------------------------------------------------------ *)
(* tail_pexpr: find the tail pure expression of an expression         *)
(*                                                                    *)
(* Returns [Some pe] when the expression's tail is [pure(pe)]        *)
(* AND no free symbol of [pe] appears in the binders accumulated      *)
(* along the linear chain leading to the tail.                        *)
(*                                                                    *)
(* The accumulator [binders] collects every symbol introduced by a   *)
(* binding pattern along the traversed chain.  At the leaf, if any  *)
(* free symbol of [pe] is in [binders] it was defined locally and    *)
(* must not escape.                                                   *)
(*                                                                    *)
(* Returns [None] for branching nodes (Eif, Ecase, Eunseq, Esave,   *)
(* Erun), actions, or when the tail pexpr is not safe to hoist.      *)
(* ------------------------------------------------------------------ *)

let rec tail_pexpr_acc binders (Expr (_, e_)) =
  match e_ with
  | Epure pe ->
      if pexpr_safe binders pe then Some pe else None
  | Ewseq (pat, _, e2) | Esseq (pat, _, e2) ->
      tail_pexpr_acc (binders_of_pat pat @ binders) e2
  | Elet (pat, _, e2) ->
      tail_pexpr_acc (binders_of_pat pat @ binders) e2
  | Ebound e | Eannot (_, e) ->
      tail_pexpr_acc binders e
  | _ ->
      None

let tail_pexpr e = tail_pexpr_acc [] e

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

  (* Replace named pattern with wildcard, extend env; node is preserved. *)
  | PElet (Pattern (p_annots, CaseBase (Some alias, cbty)),
           (Pexpr (_, _, PEsym src) as rhs),
           body) ->
      let pe_src = match Pmap.lookup src env with
                   | Some pe' -> pe'
                   | None     -> rhs in
      Pexpr (annots, bty,
        PElet (Pattern (p_annots, CaseBase (None, cbty)),
               propagate_pexpr env rhs,
               propagate_pexpr (extend_env env alias pe_src) body))

  | PElet (pat, pe1, pe2) ->
      Pexpr (annots, bty, PElet (pat,
        propagate_pexpr env pe1,
        propagate_pexpr env pe2))
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
and propagate_action env (Paction (pol, Action (loc, a, act_))) =
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
and propagate_expr env (Expr (annots, e_) as expr) =
  let pp = propagate_pexpr env in
  let pe = propagate_expr  env in
  match e_ with

  (* ---- CaseBase bindings with a named pattern.
     tail_pexpr handles both the bare pure(pe) case and the effectful-RHS
     case (where the tail is pure(pe) with all free syms of pe not locally
     bound inside e1).
     When it succeeds: replace the pattern with a wildcard, extend env, and
     propagate body.  The binding node is always preserved so that its
     annotations (source locations) are not lost.
     For Elet the RHS is a pexpr, so we match directly on PEsym.          ---- *)
  | Ewseq (Pattern (p_annots, CaseBase (Some alias, cbty)), e1, body) ->
      let e1' = propagate_expr env e1 in
      begin match tail_pexpr e1' with
      | Some pe_tail ->
          Expr (annots,
            Ewseq (Pattern (p_annots, CaseBase (None, cbty)),
                   e1',
                   propagate_expr (extend_env env alias pe_tail) body))
      | None ->
          Expr (annots,
            Ewseq (Pattern (p_annots, CaseBase (Some alias, cbty)),
                   e1',
                   propagate_expr env body))
      end

  | Esseq (Pattern (p_annots, CaseBase (Some alias, cbty)), e1, body) ->
      let e1' = propagate_expr env e1 in
      begin match tail_pexpr e1' with
      | Some pe_tail ->
          Expr (annots,
            Esseq (Pattern (p_annots, CaseBase (None, cbty)),
                   e1',
                   propagate_expr (extend_env env alias pe_tail) body))
      | None ->
          Expr (annots,
            Esseq (Pattern (p_annots, CaseBase (Some alias, cbty)),
                   e1',
                   propagate_expr env body))
      end

  | Elet (Pattern (p_annots, CaseBase (Some alias, cbty)), pe1, body) ->
      begin match pe1 with
      | Pexpr (_, _, PEsym src) ->
          let pe_src = match Pmap.lookup src env with
                       | Some pe' -> pe'
                       | None     -> pe1 in
          Expr (annots,
            Elet (Pattern (p_annots, CaseBase (None, cbty)),
                  propagate_pexpr env pe1,
                  propagate_expr (extend_env env alias pe_src) body))
      | _ ->
          Expr (annots,
            Elet (Pattern (p_annots, CaseBase (Some alias, cbty)),
                  propagate_pexpr env pe1,
                  propagate_expr env body))
      end

  (* ---- Recurse into non-matching Ewseq/Esseq/Elet nodes ---- *)
  | Ewseq (pat, e1, e2) ->
      Expr (annots, Ewseq (pat, pe e1, pe e2))
  | Esseq (pat, e1, e2) ->
      Expr (annots, Esseq (pat, pe e1, pe e2))
  | Elet (pat, pe1, e2) ->
      Expr (annots, Elet (pat, pp pe1, pe e2))

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
    | Proc (loc, mrk, bty, args, e) -> Proc (loc, mrk, bty, args, pr e)
    | decl                           -> decl in
  let rewrite_globs = function
    | GlobalDef (bty_cty, e) -> GlobalDef (bty_cty, pr e)
    | decl                   -> decl in
  { file with
    stdlib = Pmap.map rewrite_fun_map_decl file.stdlib
  ; impl   = Pmap.map rewrite_impl_decl   file.impl
  ; globs  = List.map (fun (sym, g) -> (sym, rewrite_globs g)) file.globs
  ; funs   = Pmap.map rewrite_fun_map_decl file.funs }
