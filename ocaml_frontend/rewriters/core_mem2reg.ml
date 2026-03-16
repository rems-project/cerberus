(* This file implements an analysis to find 'promotable' variables,
 * stack variables which can be promoted out of memory operations and
 * into pure Core expressions. *)
open Core

(* ------------------------------------------------------------------ *)
(* Internal classification of how a pointer sym is used               *)
(* ------------------------------------------------------------------ *)

type use =
  | Use_load    (* Load0(_, PEsym ptr, _)  — address argument *)
  | Use_store   (* Store0(_, _, PEsym ptr, _, _) — address argument *)
  | Use_kill    (* Kill(_, PEsym ptr) *)
  | Use_seqrmw  (* SeqRMW(_, _, PEsym ptr, tmp, upd) — ptr is the address argument *)
  | Use_other   (* any other occurrence *)

let use_is_promotable = function
  | Use_load | Use_store | Use_kill | Use_seqrmw -> true
  | Use_other -> false

(* ------------------------------------------------------------------ *)
(* Occurrence helpers                                                 *)
(* ------------------------------------------------------------------ *)

let is_pesym sym (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Symbol.symbolEquality s sym
  | _ -> false

let rec sym_occurs_in_pexpr sym (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Symbol.symbolEquality s sym
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ -> false
  | PEctor (_, pes) | PEcall (_, pes) | PEmemop (_, pes) ->
      List.exists (sym_occurs_in_pexpr sym) pes
  | PEcase (pe, arms) ->
      sym_occurs_in_pexpr sym pe
      || List.exists (fun (_, pe2) -> sym_occurs_in_pexpr sym pe2) arms
  | PEarray_shift (pe1, _, pe2) | PEop (_, pe1, pe2) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | PElet (_, pe1, pe2) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | PEwrapI (_, _, pe1, pe2) | PEcatch_exceptional_condition (_, _, pe1, pe2) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | PEmember_shift (pe, _, _)
  | PEconv_int (_, pe)
  | PEnot pe
  | PEis_scalar pe | PEis_integer pe | PEis_signed pe | PEis_unsigned pe
  | PEmemberof (_, _, pe) | PEunion (_, _, pe) | PEcfunction pe
  | PEbmc_assume pe ->
      sym_occurs_in_pexpr sym pe
  | PEif (pe1, pe2, pe3) ->
      sym_occurs_in_pexpr sym pe1
      || sym_occurs_in_pexpr sym pe2
      || sym_occurs_in_pexpr sym pe3
  | PEconstrained ivs ->
      List.exists (fun (_, pe) -> sym_occurs_in_pexpr sym pe) ivs
  | PEstruct (_, fields) ->
      List.exists (fun (_, pe) -> sym_occurs_in_pexpr sym pe) fields
  | PEare_compatible (pe1, pe2) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2

and sym_occurs_in_expr sym (Expr (_, e_)) =
  match e_ with
  | Epure pe -> sym_occurs_in_pexpr sym pe
  | Eaction (Paction (_, Action (_, _, act_))) ->
      sym_occurs_in_action sym act_
  | Ememop (_, pes) -> List.exists (sym_occurs_in_pexpr sym) pes
  | Ecase (pe, arms) ->
      sym_occurs_in_pexpr sym pe
      || List.exists (fun (_, e) -> sym_occurs_in_expr sym e) arms
  | Elet (_, pe, e) ->
      sym_occurs_in_pexpr sym pe || sym_occurs_in_expr sym e
  | Eif (pe, e1, e2) ->
      sym_occurs_in_pexpr sym pe
      || sym_occurs_in_expr sym e1
      || sym_occurs_in_expr sym e2
  | Eccall (_, pe1, pe2, pes) ->
      List.exists (sym_occurs_in_pexpr sym) (pe1 :: pe2 :: pes)
  | Eproc (_, _, pes) | Erun (_, _, pes) ->
      List.exists (sym_occurs_in_pexpr sym) pes
  | Eunseq es | End es | Epar es ->
      List.exists (sym_occurs_in_expr sym) es
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      sym_occurs_in_expr sym e1 || sym_occurs_in_expr sym e2
  | Ebound e | Eannot (_, e) -> sym_occurs_in_expr sym e
  | Esave (_, args, body) ->
      List.exists (fun (_, (_, pe)) -> sym_occurs_in_pexpr sym pe) args
      || sym_occurs_in_expr sym body
  | Ewait _ | Eexcluded _ -> false

and sym_occurs_in_action sym act_ =
  match act_ with
  | Create (pe1, pe2, _) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | CreateReadOnly (pe1, pe2, pe3, _) ->
      sym_occurs_in_pexpr sym pe1
      || sym_occurs_in_pexpr sym pe2
      || sym_occurs_in_pexpr sym pe3
  | Alloc0 (pe1, pe2, _) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | Kill (_, pe) -> sym_occurs_in_pexpr sym pe
  | Load0 (_, pe, _) -> sym_occurs_in_pexpr sym pe
  | Store0 (_, pe1, pe2, pe3, _) ->
      sym_occurs_in_pexpr sym pe1
      || sym_occurs_in_pexpr sym pe2
      || sym_occurs_in_pexpr sym pe3
  | Fence0 _ -> false
  | SeqRMW (_, pe1, pe2, _, pe3) ->
      sym_occurs_in_pexpr sym pe1
      || sym_occurs_in_pexpr sym pe2
      || sym_occurs_in_pexpr sym pe3
  | RMW0 (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeStrong (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeWeak (pe1, pe2, pe3, pe4, _, _) ->
      List.exists (sym_occurs_in_pexpr sym) [pe1; pe2; pe3; pe4]
  | LinuxFence _ -> false
  | LinuxLoad (pe1, pe2, _) ->
      sym_occurs_in_pexpr sym pe1 || sym_occurs_in_pexpr sym pe2
  | LinuxStore (pe1, pe2, pe3, _) | LinuxRMW (pe1, pe2, pe3, _) ->
      List.exists (sym_occurs_in_pexpr sym) [pe1; pe2; pe3]

(* ------------------------------------------------------------------ *)
(* Classify a single action's uses of sym                             *)
(* Only plain uses of the symbol are allowed - e.g. member shifts are *)
(* counted as other uses and not promoted.                            *)
(* ------------------------------------------------------------------ *)

let classify_action sym act_ : use list =
  match act_ with
  | Store0 (_, _ctype_pe, addr_pe, val_pe, _) ->
      let addr_use =
        if is_pesym sym addr_pe then [Use_store]
        else if sym_occurs_in_pexpr sym addr_pe then [Use_other]
        else []
      in
      let val_use =
        if sym_occurs_in_pexpr sym val_pe then [Use_other] else []
      in
      addr_use @ val_use
  | Load0 (_ctype_pe, addr_pe, _) ->
      if is_pesym sym addr_pe then [Use_load]
      else if sym_occurs_in_pexpr sym addr_pe then [Use_other]
      else []
  | Kill (_, addr_pe) ->
      if is_pesym sym addr_pe then [Use_kill]
      else if sym_occurs_in_pexpr sym addr_pe then [Use_other]
      else []
  | SeqRMW (_, _ty_pe, addr_pe, _tmp_sym, upd_pe) ->
      let addr_use =
        if is_pesym sym addr_pe then
          [Use_seqrmw]
        else if sym_occurs_in_pexpr sym addr_pe then
          (* I think the elaboration ensures this case is impossible *)
          [Use_other]
        else
          []
      in
      let upd_use =
        if sym_occurs_in_pexpr sym upd_pe then [Use_other] else []
      in
      addr_use @ upd_use
  | _ ->
      if sym_occurs_in_action sym act_ then [Use_other] else []

(* ------------------------------------------------------------------ *)
(* collect_uses: gather all uses of sym in an expression              *)
(* ------------------------------------------------------------------ *)

let rec collect_uses sym (Expr (_, e_)) : use list =
  match e_ with
  | Eaction (Paction (_, Action (_, _, act_))) ->
      classify_action sym act_
  | Esave (_, args, body) ->
      (* Conservative: any occurrence inside an Esave is Use_other,
         since loop bodies may re-enter and store to the variable. *)
      let in_args =
        List.exists (fun (_, (_, pe)) -> sym_occurs_in_pexpr sym pe) args
      in
      let in_body = sym_occurs_in_expr sym body in
      if in_args || in_body then [Use_other] else []
  | Epure pe ->
      if sym_occurs_in_pexpr sym pe then [Use_other] else []
  | Ememop (_, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) pes then [Use_other] else []
  | Elet (_, pe, e) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ collect_uses sym e
  | Ecase (pe, arms) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ List.concat_map (fun (_, e) -> collect_uses sym e) arms
  | Eif (pe, e1, e2) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ collect_uses sym e1
      @ collect_uses sym e2
  | Eccall (_, fn_pe, arg_pe, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) (fn_pe :: arg_pe :: pes)
      then [Use_other] else []
  | Eproc (_, _, pes) | Erun (_, _, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) pes then [Use_other] else []
  | Eunseq es | End es | Epar es ->
      List.concat_map (collect_uses sym) es
  | Ewseq (
      Pattern (_, CaseBase (Some alias_sym, _)),
      Expr (_, Epure (Pexpr (_, _, PEsym src_sym))),
      body
    ) when Symbol.symbolEquality src_sym sym ->
      (* Core pattern: let weak alias = pure(sym) in body.
         sym is being used as a pointer value to be copied into alias.
         Classify sym's use here based on how alias is used in body. *)
      collect_uses alias_sym body
      @ collect_uses sym body
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      collect_uses sym e1 @ collect_uses sym e2
  | Ebound e | Eannot (_, e) -> collect_uses sym e
  | Ewait _ | Eexcluded _ -> []

(* collect_creates finds Create-bound syms that are candidates for
   promotion.  Under Normal_callconv only PrefSource (C local variables)
   are considered; under Inner_arg_callconv PrefFunArg (callee-owned
   parameter temporaries) are also included, since in that convention
   the callee creates and owns the argument slot.                      *)

let rec collect_creates ~also_fun_args (Expr (_, e_)) : Symbol.sym list =
  match e_ with
  | Esseq (
      Pattern (_, CaseBase (Some ptr_sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefSource _))))),
      body
    ) ->
      ptr_sym :: collect_creates ~also_fun_args body
  | Esseq (
      Pattern (_, CaseBase (Some ptr_sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefFunArg _))))),
      body
    ) when also_fun_args ->
      ptr_sym :: collect_creates ~also_fun_args body
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      collect_creates ~also_fun_args e1 @ collect_creates ~also_fun_args e2
  | Elet (_, _, e) | Ebound e | Eannot (_, e) ->
      collect_creates ~also_fun_args e
  | Eif (_, e1, e2) ->
      collect_creates ~also_fun_args e1 @ collect_creates ~also_fun_args e2
  | Ecase (_, arms) ->
      List.concat_map (fun (_, e) -> collect_creates ~also_fun_args e) arms
  | Esave (_, _, body) ->
      collect_creates ~also_fun_args body
  | Eunseq es | End es | Epar es ->
      List.concat_map (collect_creates ~also_fun_args) es
  | Epure _ | Eaction _ | Ememop _ | Eccall _ | Eproc _
  | Erun _ | Ewait _ | Eexcluded _ -> []

(* ------------------------------------------------------------------ *)
(* check_definitely_init                                               *)
(*                                                                     *)
(* Returns (safe, init_after):                                         *)
(*   safe       – no load-before-store on any syntactic path           *)
(*   init_after – on ALL paths through expr, at least one store        *)
(*                has occurred (so a subsequent load would be safe)    *)
(* ------------------------------------------------------------------ *)

let rec check_definitely_init sym already_init (Expr (_, e_)) =
  match e_ with
  | Eaction (Paction (_, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, _, _) when is_pesym sym addr_pe ->
          (true, true)
      | Load0 (_, addr_pe, _) when is_pesym sym addr_pe ->
          (already_init, already_init)
      | Kill (_, addr_pe) when is_pesym sym addr_pe ->
          (true, false)
      | SeqRMW (_, _, addr_pe, _, _) when is_pesym sym addr_pe ->
          (* Atomically reads then writes: safe iff already_init; always
             initialises after. *)
          (already_init, true)
      | _ ->
          (true, already_init)
      end
  | Esseq (_, e1, e2) ->
      let (s1, ia1) = check_definitely_init sym already_init e1 in
      let (s2, ia2) = check_definitely_init sym ia1 e2 in
      (s1 && s2, ia2)
  | Ewseq (_, e1, e2) ->
      (* Neg actions in e1 are NOT sequenced before e2, so e2 cannot
         rely on stores in e1.  Pass already_init (not ia1) to e2. *)
      let (s1, ia1) = check_definitely_init sym already_init e1 in
      let (s2, ia2) = check_definitely_init sym already_init e2 in
      (s1 && s2, ia1 || ia2)
  | Eunseq arms ->
      (* No arm's result is visible to any sibling arm. *)
      let results = List.map (check_definitely_init sym already_init) arms in
      let safe      = List.for_all (fun (s, _) -> s) results in
      let init_after = List.for_all (fun (_, ia) -> ia) results in
      (safe, init_after)
  | Eif (_, et, ef) ->
      let (st, iat) = check_definitely_init sym already_init et in
      let (sf, iaf) = check_definitely_init sym already_init ef in
      (st && sf, iat && iaf)
  | Ecase (_, arms) ->
      let results =
        List.map (fun (_, e) -> check_definitely_init sym already_init e) arms
      in
      let safe       = List.for_all (fun (s, _) -> s) results in
      let init_after = List.for_all (fun (_, ia) -> ia) results in
      (safe, init_after)
  | Esave (_, args, body) ->
      (* Conservative: a loop may re-enter without re-running the store. *)
      if List.exists (fun (_, (_, pe)) -> sym_occurs_in_pexpr sym pe) args
         || sym_occurs_in_expr sym body
      then (false, already_init)
      else (true, already_init)
  | Elet (_, _, e) | Ebound e | Eannot (_, e) ->
      check_definitely_init sym already_init e
  | _ ->
      (true, already_init)

(* ------------------------------------------------------------------ *)
(* expr_writes_sym: does expr contain a Store0 or SeqRMW whose        *)
(* address is directly PEsym sym?                                      *)
(* ------------------------------------------------------------------ *)

let rec expr_writes_sym sym (Expr (_, e_)) =
  match e_ with
  | Eaction (Paction (_, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, _, _) -> is_pesym sym addr_pe
      | SeqRMW (_, _, addr_pe, _, _) -> is_pesym sym addr_pe
      | _ -> false
      end
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      expr_writes_sym sym e1 || expr_writes_sym sym e2
  | Eunseq es | End es | Epar es ->
      List.exists (expr_writes_sym sym) es
  | Eif (_, e1, e2) ->
      expr_writes_sym sym e1 || expr_writes_sym sym e2
  | Ecase (_, arms) ->
      List.exists (fun (_, e) -> expr_writes_sym sym e) arms
  | Elet (_, _, e) | Ebound e | Eannot (_, e) ->
      expr_writes_sym sym e
  | Esave (_, _, body) ->
      expr_writes_sym sym body
  | _ -> false

(* ------------------------------------------------------------------ *)
(* no_mixed_unseq_uses                                                 *)
(*                                                                     *)
(* Returns false if sym appears in a write arm AND ≥2 arms of any     *)
(* Eunseq mention sym — which would mean promoting sym silently        *)
(* removes a Store0/SeqRMW that Cerberus's sequencing-violation        *)
(* detector would otherwise see.                                       *)
(* ------------------------------------------------------------------ *)

let rec no_mixed_unseq_uses sym (Expr (_, e_)) =
  match e_ with
  | Eunseq arms ->
      let writing_arms   = List.filter (expr_writes_sym sym) arms in
      let mentioning_arms = List.filter (sym_occurs_in_expr sym) arms in
      let conflict = (match writing_arms with [] -> false | _ -> true)
                     && List.length mentioning_arms >= 2 in
      (not conflict) && List.for_all (no_mixed_unseq_uses sym) arms
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      no_mixed_unseq_uses sym e1 && no_mixed_unseq_uses sym e2
  | Eif (_, e1, e2) ->
      no_mixed_unseq_uses sym e1 && no_mixed_unseq_uses sym e2
  | Ecase (_, arms) ->
      List.for_all (fun (_, e) -> no_mixed_unseq_uses sym e) arms
  | Elet (_, _, e) | Ebound e | Eannot (_, e) ->
      no_mixed_unseq_uses sym e
  | Esave (_, _, body) ->
      no_mixed_unseq_uses sym body
  | End es | Epar es ->
      List.for_all (no_mixed_unseq_uses sym) es
  | _ -> true

(* ------------------------------------------------------------------ *)
(* Promotability analysis for a single procedure                       *)
(* ------------------------------------------------------------------ *)

let find_promotable ~also_fun_args f_sym body : Symbol.sym list =
  let creates = collect_creates ~also_fun_args body in
  let is_promotable s =
    List.for_all use_is_promotable (collect_uses s body)
    && fst (check_definitely_init s false body)
    && no_mixed_unseq_uses s body
  in
  let promotable = List.filter is_promotable creates in
  Cerb_debug.print_debug 3 [] (fun () ->
    Printf.sprintf "[mem2reg] %s: %d promotable: [%s]"
      (Pp_symbol.to_string_pretty f_sym)
      (List.length promotable)
      (String.concat ", " (List.map Pp_symbol.to_string_pretty promotable)));
  promotable

(* ------------------------------------------------------------------ *)
(* transform_file: analysis phase only — file returned unchanged       *)
(* ------------------------------------------------------------------ *)

let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  List.iter (fun (f_sym, decl) ->
    match decl with
    | Proc (_, _, _, _, body) ->
        ignore (find_promotable ~also_fun_args f_sym body)
    | Fun _ | ProcDecl _ | BuiltinDecl _ -> ()
  ) (Pmap.bindings_list file.funs);
  file
