open Core

type env = (Symbol.sym, pexpr) Pmap.map

let empty_env : env = Pmap.empty Symbol.compare_sym

let extend_env env alias pe = Pmap.add alias pe env

let extend_env_list env bindings =
  List.fold_left (fun acc (s, pe) -> extend_env acc s pe) env bindings

let sym_in binders s =
  List.exists (fun b -> Symbol.compare_sym s b = 0) binders

(* a conservative free-variable and replaceable-with-unit check

   no free variables because the expression will be substituted (propagated)
   into other contexts so needs to be well-formed

   replaceable with unit is more a matter of taste - we don't want large
   pure expressions repeated throughout the code, such as if, let, case,
   ccall; also simpler to not check if, let and case more precisely

   cfunction always returns a tuple when evaluated so it's not worth checking
   (i.e. analyze_pat_expr would always skip it) *)

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

(* ------------------------------------------------------------------ *)
(* analyze_pat_pexpr: pattern-aware single-pass analysis for pexprs   *)
(*                                                                    *)
(* Takes the binding pattern alongside the RHS pure expression and    *)
(* returns a coherent triple (bindings, new_pat, new_pe) where        *)
(* new_pat and new_pe are type-compatible with each other.            *)
(* ------------------------------------------------------------------ *)

let is_integer_annot = function
  | Annot.Avalue (Ainteger ity) -> Some ity
  | _ -> None

let remove_integer_annot annots =
  List.filter (fun a -> Option.is_none (is_integer_annot a)) annots

(* integer annotations are used to figure out bit-vector (checking)
 * types for pure expressions, of various kinds, so must be removed
 * from units *)
let unit_pexpr (Pexpr (annots, bty, _)) =
  Pexpr (remove_integer_annot annots, bty, PEval Vunit)

let wildcard_pat (Pattern (p_annots, _)) =
  Pattern (p_annots, CaseBase (None, BTy_unit))

let unit_pat_pe pat pe =
  let Pattern (p_annots, pat_) = pat in
  let Pexpr (annots, bty, pe_) = pe in
  match pat_, pe_ with
  | CaseBase (_, BTy_unit), PEval Vunit ->
    true
  | _ ->
    false

(* integer annotations are sometimes placed on the outside of an
   expression, such as
   {- cn_value: signed int -}pure(Specified(4))

   during pattern matching and substitution, these must be pushed
   in so that the substitution expression also carries the same *)
let push_integer_annot annot pexpr =
  match List.filter_map is_integer_annot annot with
  | [] -> pexpr
  | _ :: _ as itys ->
    let annots = List.map (fun x -> Annot.Avalue (Ainteger x)) itys in
    (* see https://github.com/rems-project/cerberus/issues/1000 *)
    let Pexpr (inner_annots, inner_bty, inner_pe_) = pexpr in
    Pexpr (annots @ inner_annots, inner_bty, inner_pe_)

let rec analyze_pat_pexpr binders pat pe =
  let Pattern (p_annots, pat_) = pat in
  match pat_, pe with

  | CaseBase (Some s, _), _ when can_prop_and_rm binders pe ->
      ([(s, pe)], wildcard_pat pat, unit_pexpr pe)

  | CaseBase (None, _), _ when can_prop_and_rm binders pe ->
      ([], wildcard_pat pat, unit_pexpr pe)

  | CaseBase (_, _), _ ->
      ([], pat, pe)

  | CaseCtor (Ctuple, pats), Pexpr (pe_annots, pe_bty, PEctor (Ctuple, pes))
    when List.length pats = List.length pes ->
      let results = List.map2 (analyze_pat_pexpr binders) pats pes in
      let bindings  = List.concat_map (fun (bs, _, _) -> bs) results in
      let new_pats  = List.map (fun (_, p, _) -> p) results in
      let new_pes   = List.map (fun (_, _, e) -> e) results in
      ( bindings
      , Pattern (p_annots, CaseCtor (Ctuple, new_pats))
      , Pexpr (pe_annots, pe_bty, PEctor (Ctuple, new_pes)) )

  | CaseCtor (Cspecified, [inner_pat]),
    Pexpr (pe_annots, pe_bty, PEctor (Cspecified, [inner_pe])) ->
      analyse_specified_pat_expr binders (p_annots, inner_pat) (pe_annots, pe_bty, inner_pe)

  | CaseCtor (Cspecified, [inner_pat]),
    Pexpr (pe_annots, pe_bty, PEval (Vloaded (LVspecified ov))) ->
      let inner_pe = Pexpr (pe_annots, pe_bty, PEval (Vobject ov)) in
      analyse_specified_pat_expr binders (p_annots, inner_pat) (pe_annots, pe_bty, inner_pe)

  | _ ->
      ([], pat, pe)

and analyse_specified_pat_expr binders (p_annots, inner_pat) (pe_annots, pe_bty, inner_pe) =
  (* so that the subsitution gets any annotations *)
  let inner_pe = push_integer_annot pe_annots inner_pe in
  let (bindings, new_inner_pat, new_inner_pe) =
    analyze_pat_pexpr binders inner_pat inner_pe in
  if unit_pat_pe new_inner_pat new_inner_pe then
    let Pexpr (inner_annots, inner_bty, inner_pe_) = new_inner_pe in
    (* but unit values have such annotations removed *)
    let annots = remove_integer_annot (pe_annots @ inner_annots) in
    let new_inner_pe = Pexpr (annots, inner_bty, inner_pe_) in
    ( bindings , new_inner_pat , new_inner_pe )
  else
    (* if it's already been pushed inside, the outer will duplicate it *)
    let pe_annots = remove_integer_annot pe_annots in
    ( bindings
    , Pattern (p_annots, CaseCtor (Cspecified, [new_inner_pat]))
    , Pexpr (pe_annots, pe_bty, PEctor (Cspecified, [new_inner_pe])) )


(* ------------------------------------------------------------------ *)
(* analyze_pat_expr: pattern-aware single-pass analysis for exprs     *)
(*                                                                    *)
(* Descends through sequential chains to find the tail Epure, then    *)
(* delegates to analyze_pat_pexpr. Returns (bindings, new_pat, new_e  *)
(* where new_pat and new_e are type-compatible.                       *)
(* ------------------------------------------------------------------ *)

let push_loc_annot annot pexpr =
  match List.filter (function Annot.Aloc _ -> true | _ -> false)  annot with
  | [] -> pexpr
  | [ loc ] ->
    let Pexpr (inner_annots, inner_bty, inner_pe_) = pexpr in
    Pexpr (loc :: inner_annots, inner_bty, inner_pe_)
  | _ :: _ :: _ -> assert (false)

(* a bit cheeky, but works well:

   let x: loaded integer = load(..) in
   let Specified(x2 : integer) = x in ..
   ==>
   let Specified(x : integer) = load(..) in
   let _: unit = Unit in .. *)

let unwrap_loaded_pat ~enabled (subs, pat, expr) =
  if enabled then
    let Pattern (p_annots, pat_) = pat in
    (match pat_ with
     | CaseBase (Some s, BTy_loaded cbt) ->
         let pe_sym = Pexpr ([], (), PEsym s) in
         let pe = Pexpr ([], (), PEctor (Cspecified, [pe_sym])) in
         let pattern = Pattern ([], CaseBase (Some s, BTy_object cbt)) in
         let pattern = Pattern (p_annots, CaseCtor (Cspecified, [pattern])) in
         (* re-using the same sym! *)
         ((s, pe) :: subs, pattern, expr)
     | _ ->
         (subs, pat, expr))
  else
    (subs, pat, expr)

let rec analyze_pat_expr ~unwrap_loaded binders pat (Expr (annot, e_) as expr) =
  let analyze = analyze_pat_expr ~unwrap_loaded in
  let ret_e e_ = Expr (annot, e_) in
  match e_ with
  | Epure pe ->
      (* so that the subsitution gets any annotations *)
      let pe = push_integer_annot annot pe in
      let pe = push_loc_annot annot pe in
      let (bs, new_pat, new_pe) = analyze_pat_pexpr binders pat pe in
      (* if it's already been pushed inside, the outer will duplicate it *)
      unwrap_loaded_pat
        ~enabled:unwrap_loaded
        (bs, new_pat, Expr (remove_integer_annot annot, Epure new_pe))

  | Eunseq es ->
      let Pattern (p_annots, pat_) = pat in
      (match pat_ with
       | CaseCtor (Ctuple, pats) when List.length pats = List.length es ->
           let results = List.map2 (analyze binders) pats es in
           let bindings = List.concat_map (fun (bs, _, _) -> bs) results in
           let new_pats = List.map (fun (_, p, _) -> p) results in
           let new_es   = List.map (fun (_, _, e) -> e) results in
           ( bindings
           , Pattern (p_annots, CaseCtor (Ctuple, new_pats))
           , ret_e (Eunseq new_es) )
       | _ ->
           ([], pat, expr))

  | Ewseq (inner_pat, e1, e2) ->
      let binders' = binders_of_pat inner_pat @ binders in
      let (bs, new_outer_pat, new_e2) = analyze binders' pat e2 in
      (bs, new_outer_pat, ret_e (Ewseq (inner_pat, e1, new_e2)))

  | Esseq (inner_pat, e1, e2) ->
      let binders' = binders_of_pat inner_pat @ binders in
      let (bs, new_outer_pat, new_e2) = analyze binders' pat e2 in
      (bs, new_outer_pat, ret_e (Esseq (inner_pat, e1, new_e2)))

  | Elet (inner_pat, pe1, e2) ->
      let binders' = binders_of_pat inner_pat @ binders in
      let (bs, new_outer_pat, new_e2) = analyze binders' pat e2 in
      (bs, new_outer_pat, ret_e (Elet (inner_pat, pe1, new_e2)))

  | Ebound e ->
      let (bs, new_pat, new_e) = analyze binders pat e in
      (bs, new_pat, ret_e (Ebound new_e))

  | Eannot (al, e) ->
      let (bs, new_pat, new_e) = analyze binders pat e in
      (bs, new_pat, ret_e (Eannot (al, new_e)))

  | _ ->
      unwrap_loaded_pat ~enabled:unwrap_loaded ([], pat, expr)

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
      let (bindings, new_pat, pe1'') = analyze_pat_pexpr [] pat pe1' in
      let env' = extend_env_list env bindings in
      Pexpr (annots, bty, PElet (new_pat, pe1'', propagate_pexpr env' pe2))
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
let rec propagate_expr ~unwrap_loaded env (Expr (annots, e_) as expr) =
  let pp = propagate_pexpr env in
  let propagate = propagate_expr ~unwrap_loaded in
  match e_ with
  | Ewseq (pat, e1, body) ->
      let e1' = propagate env e1 in
      let (bindings, new_pat, e1'') = analyze_pat_expr ~unwrap_loaded [] pat e1' in
      let env' = extend_env_list env bindings in
      Expr (annots, Ewseq (new_pat, e1'', propagate env' body))

  | Esseq (pat, e1, body) ->
      let e1' = propagate env e1 in
      let (bindings, new_pat, e1'') = analyze_pat_expr ~unwrap_loaded [] pat e1' in
      let env' = extend_env_list env bindings in
      Expr (annots, Esseq (new_pat, e1'', propagate env' body))

  | Elet (pat, pe1, body) ->
      let pe1' = propagate_pexpr env pe1 in
      let (bindings, new_pat, pe1'') = analyze_pat_pexpr [] pat pe1' in
      let env' = extend_env_list env bindings in
      Expr (annots, Elet (new_pat, pe1'', propagate env' body))

  (* ---- Other expression forms: recurse ---- *)
  | Epure pe1 ->
      Expr (annots, Epure (pp pe1))
  | Ememop (op, pes) ->
      Expr (annots, Ememop (op, List.map pp pes))
  | Eaction pact ->
      Expr (annots, Eaction (propagate_action env pact))
  | Ecase (pe1, arms) ->
      Expr (annots, Ecase (pp pe1,
        List.map (fun (pat, e2) -> (pat, propagate env e2)) arms))
  | Eif (pe1, e1, e2) ->
      Expr (annots, Eif (pp pe1, propagate env e1, propagate env e2))
  | Eccall (a, pe1, pe2, pes) ->
      Expr (annots, Eccall (a, pp pe1, pp pe2, List.map pp pes))
  | Eproc (a, name, pes) ->
      Expr (annots, Eproc (a, name, List.map pp pes))
  | Eunseq es ->
      Expr (annots, Eunseq (List.map (propagate env) es))
  | Esave (sym_bty, args, body) ->
      Expr (annots, Esave (sym_bty,
        List.map (fun (s, (type_info, pe1)) -> (s, (type_info, pp pe1))) args,
        propagate env body))
  | Erun (a, lbl, pes) ->
      Expr (annots, Erun (a, lbl, List.map pp pes))
  | Ebound e ->
      Expr (annots, Ebound (propagate env e))
  | Eannot (fps, e) ->
      Expr (annots, Eannot (fps, propagate env e))
  | End es ->
      Expr (annots, End (List.map (propagate env) es))
  | Epar es ->
      Expr (annots, Epar (List.map (propagate env) es))
  | Ewait _ ->
      expr
  | Eexcluded _ ->
      expr

let transform_file ~unwrap_loaded file =
  let pr e  = propagate_expr ~unwrap_loaded  empty_env e in
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
