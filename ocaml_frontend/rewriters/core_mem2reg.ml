(* This file implements an analysis to find 'promotable' variables,
   stack variables which can be promoted out of memory operations and
   into pure Core expressions. *)
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

let addr_not_taken = function
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

let sym_occurs_in_action sym act_ =
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
        if is_pesym sym addr_pe then [Use_seqrmw]
        else if sym_occurs_in_pexpr sym addr_pe then [Use_other]
        else []
      in
      let upd_use =
        if sym_occurs_in_pexpr sym upd_pe then [Use_other] else []
      in
      addr_use @ upd_use
  | _ ->
      if sym_occurs_in_action sym act_ then [Use_other] else []

(* ------------------------------------------------------------------ *)
(* Esave memo tables                                                  *)
(*                                                                    *)
(* Both collect_uses and sequentialisable need to analyse Esave       *)
(* bodies: once via the default args and once per Erun call site.     *)
(* Results are memoised per (label_sym, param_sym) to avoid redundant *)
(* traversals and to terminate on back-edge Eruns.                    *)
(* ------------------------------------------------------------------ *)

type 'a esave_memo_entry = {
  params  : (Symbol.sym * pexpr) list;            (* (param_sym, default_pe) by position *)
  body    : (unit, unit, Symbol.sym) generic_expr;
  results : (Symbol.sym, 'a) Pmap.map ref;        (* param_sym -> cached result, filled lazily *)
}

(* 'a = use list                              for collect_uses          *)
(* 'a = bool * (Event_set.t * env) option  for sequentialisable   *)
type 'a memo_save_info = (Symbol.sym, 'a esave_memo_entry) Pmap.map

(* find_single_direct_alias sym pairs:
   Given an association list of (param_sym, pe) pairs, returns:
     None           — sym does not appear as a bare PEsym in any pe
     Some param_sym — sym appears as a bare PEsym in exactly one pe
   Raises failwith if sym appears in more than one pe (invariant violation). *)
let find_single_direct_alias sym pairs =
  match List.filter_map (fun (param_sym, pe) ->
    if is_pesym sym pe then Some param_sym else None) pairs
  with
  | []          -> None
  | [param_sym] -> Some param_sym
  | _ :: _ :: _ -> failwith "Core_mem2reg: multiple direct aliases for the same sym"

(* collect_esave_defs: pre-walk the function body collecting all Esave
   definitions into a memo table. *)
let collect_esave_defs body =
  (* Pre-walk: collect all Esave definitions *)
  let memo = ref (Pmap.empty Symbol.compare_sym) in
  let rec walk (Expr (_, e_)) =
    match e_ with
    | Esave ((label_sym, _), params, esave_body) ->
        let entry = {
          params  = List.map (fun (s, (_, pe)) -> (s, pe)) params;
          body    = esave_body;
          results = ref (Pmap.empty Symbol.compare_sym);
        } in
        memo := Pmap.add label_sym entry !memo;
        walk esave_body
    | Ewseq (_, e1, e2) | Esseq (_, e1, e2) -> walk e1; walk e2
    | Eif (_, e1, e2)                        -> walk e1; walk e2
    | Ecase (_, arms)   -> List.iter (fun (_, e) -> walk e) arms
    | Elet (_, _, e) | Ebound e | Eannot (_, e) -> walk e
    | Eunseq es | End es | Epar es           -> List.iter walk es
    | Epure _ | Eaction _ | Ememop _ | Eccall _ | Eproc _
    | Erun _ | Ewait _ | Eexcluded _        -> ()
  in
  walk body;
  !memo

(* ------------------------------------------------------------------- *)
(* collect_uses: gather all uses of sym in an expression               *)
(*                                                                     *)
(* Key invariant (guaranteed by elaboration): for any CREATE-bound     *)
(* local pointer sym `s`, if `s` appears in an Esave body, then `s`    *)
(* is passed as a direct PEsym default arg to that Esave.  This means  *)
(* the case when `find_single_direct_alias` returns None is sound: if  *)
(* `s` is not in any param, it cannot appear in the body as an address *)
(* of a Load/Store/Kill. 					       *)
(*                                                                     *)
(* Non-pointer syms (e.g., globals, or function parameters in the      *)
(* Normal_callconv) may appear freely in Esave bodies and are not      *)
(* mem2reg candidates; they do not affect this analysis.               *)
(*                                                                     *)
(* Symbol rebindings/aliases in let/wseq/sseq are eliminated by the    *)
(* copy_prop pass (required/assumed) and so we can be naive here.      *)
(* ------------------------------------------------------------------- *)

let rec collect_uses use_memo sym (Expr (_, e_)) : use list =
  match e_ with
  | Eaction (Paction (_, Action (_, _, act_))) ->
      classify_action sym act_
  | Esave ((label_sym, _), params, _body) ->
      (* All default args are bare PEsym by the closedness check.
         Closedness also guarantees sym is not free in body unless it is a param. *)
      let entry = Pmap.find label_sym use_memo in
      (match find_single_direct_alias sym
               (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
      | None           -> []
      | Some param_sym ->
          (match Pmap.lookup param_sym !(entry.results) with
          | Some cached -> cached
          | None ->
              entry.results := Pmap.add param_sym [] !(entry.results);
              let result = collect_uses use_memo param_sym entry.body in
              entry.results := Pmap.add param_sym result !(entry.results);
              result))
  | Erun (_, label_sym, args) ->
      (* Closedness guarantees args matching sym are direct PEsym aliases. *)
      let entry = Pmap.find label_sym use_memo in
      (match find_single_direct_alias sym
               (List.combine (List.map fst entry.params) args) with
      | None           -> []
      | Some param_sym ->
          (match Pmap.lookup param_sym !(entry.results) with
          | Some cached -> cached
          | None ->
              entry.results := Pmap.add param_sym [] !(entry.results);
              let result = collect_uses use_memo param_sym entry.body in
              entry.results := Pmap.add param_sym result !(entry.results);
              result))
  | Epure pe ->
      if sym_occurs_in_pexpr sym pe then [Use_other] else []
  | Ememop (_, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) pes then [Use_other] else []
  | Elet (_, pe, e) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ collect_uses use_memo sym e
  | Ecase (pe, arms) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ List.concat_map (fun (_, e) -> collect_uses use_memo sym e) arms
  | Eif (pe, e1, e2) ->
      (if sym_occurs_in_pexpr sym pe then [Use_other] else [])
      @ collect_uses use_memo sym e1
      @ collect_uses use_memo sym e2
  | Eccall (_, fn_pe, arg_pe, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) (fn_pe :: arg_pe :: pes)
      then [Use_other] else []
  | Eproc (_, _, pes) ->
      if List.exists (sym_occurs_in_pexpr sym) pes then [Use_other] else []
  | Eunseq es | End es | Epar es ->
      List.concat_map (collect_uses use_memo sym) es
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      collect_uses use_memo sym e1 @ collect_uses use_memo sym e2
  | Ebound e | Eannot (_, e) -> collect_uses use_memo sym e
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
(* sequentialisable: unified promotability analysis                    *)
(*                                                                     *)
(* Returns:                                                            *)
(*   None           — all control-flow paths end in Erun (vacuous)    *)
(*   Some (ev, env') — events observed on sym and env after expr      *)
(* Raises Not_sequentialisable on any conflict.                        *)
(* Raises Load_from_uninit when a Load0/SeqRMW sees env=Uninit;       *)
(*   caught by save_param_needs_init to detect loops that need init.        *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Event: memory events observable on a single sym                *)
(* ------------------------------------------------------------------ *)

module Event = struct
  type t = Pos_store | Neg_store | Load | Kill
  let is_neg_store = function Neg_store -> true | _ -> false
  let is_load = function Load -> true | _ -> false
  let compare x y =
    let num = function
    | Pos_store -> 0
    | Neg_store -> 1
    | Load -> 2
    | Kill -> 3 in
    Int.compare (num x) (num y)
end

module Event_set = Set.Make(Event)

(* env: initialization state of sym at a given program point          *)
(* Uninit      — no store observed yet on this path                   *)
(* Init pe     — sym was last stored with committed value pe          *)
(* Killed      — sym's allocation was freed                           *)
type env = Uninit | Init of pexpr | Killed
let is_uninit = function Uninit -> true | _ -> false
let is_killed = function Killed -> true | _ -> false

exception Not_sequentialisable
exception Load_from_uninit

let ( let* ) = Option.bind


(* combine_branches pe_cond r1 r2: merge results from two branches.
   pe_cond is used to construct PEif for the merged Init pexpr. *)
let combine_branches pe_cond r1 r2 =
  match r1, r2 with
  | None, None -> None
  | None, (Some _ as result) | (Some _ as result), None -> result
  | Some (ev1, env1), Some (ev2, env2) ->
    let combined_env = match env1, env2 with
      | Uninit, Uninit -> Uninit
      | Killed, Killed -> Killed
      | Init pe1, Init pe2 ->
          Init (Pexpr ([], (), PEif (pe_cond, pe1, pe2)))
      | _ -> raise Not_sequentialisable
    in
    Some (Event_set.union ev1 ev2, combined_env)

(* combine_case_branches pe arm_results:
   Merges sequentialisable results from Ecase arms, building a PEcase node for
   the Init env. pe is the case discriminant pexpr.
   arm_results : (pattern * (Event_set.t * env) option) list

   Note: arms whose result is None (all paths end in Erun) are handled as if
   having no events and producing UB, for the sake of combining values into
   one case-pexpr and retaining pattern-completeness. *)
let combine_case_branches pe arm_results =
  let here = Cerb_location.other __LOC__ in
  let ub = Undefined.DUMMY "core_mem2reg: branch assumed to not return" in
  let undef = Pexpr ([], (), PEundef (here, ub)) in
  let branches =
    List.map
      (fun (pat, r) ->
         match r with
         | None -> (pat, (Event_set.empty, Init undef))
         | Some x -> (pat, x))
      arm_results in
  let all_evs = List.map (fun (_, (ev, _)) -> ev) branches in
  let all_evs = List.fold_left Event_set.union Event_set.empty all_evs in
  let all_uninit = List.for_all (fun (_, (_, e)) -> is_uninit e) branches in
  let all_killed = List.for_all (fun (_, (_, e)) -> is_killed e) branches in
  let combined_env =
    if all_uninit then
      Uninit
    else if all_killed then
      Killed
    else
      let pe_arms =
        List.map (fun (pat, (_, e)) ->
            match e with
            | Init pe2 -> (pat, pe2)
            | _ -> raise Not_sequentialisable) branches in
      Init (Pexpr ([], (), PEcase (pe, pe_arms))) in
  Some (all_evs, combined_env)

(* seq_memo: memoises sequentialisable results per (label_sym, param_sym).
   'a = bool * (Event_set.t * env) option
     fst = init_needed: body requires Init _ env on entry (true) or
           self-initialises (false)
     snd = None while in progress or all paths end in Erun;
           Some (ev, env') otherwise *)
type seq_memo = (bool * (Event_set.t * env) option) memo_save_info

let rec sequentialisable (seq_memo : seq_memo) sym env (Expr (_, e_))
    : (Event_set.t * env) option =
  let module Es = Event_set in
  match e_ with
  | Eaction (Paction (polarity, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, val_pe, _) when is_pesym sym addr_pe ->
          let ev = match polarity with
            | Pos -> Event.Pos_store
            | Neg -> Event.Neg_store in
        Some (Es.singleton ev, Init val_pe)
      | Load0 (_, addr_pe, _) when is_pesym sym addr_pe ->
          (match env with
           | Init _ -> Some (Es.singleton Event.Load, env)
           | Uninit  -> raise Load_from_uninit
           | Killed  -> raise Not_sequentialisable)
      | Kill (_, addr_pe) when is_pesym sym addr_pe ->
          Some (Es.singleton Event.Kill, Killed)
      | SeqRMW (_, _, addr_pe, tmp_sym, upd_pe) when is_pesym sym addr_pe ->
          (match env with
           | Init pe ->
               let stored = Core_aux.unsafe_subst_sym_pexpr tmp_sym pe upd_pe in
               Some (Es.of_list [Event.Load; Event.Pos_store], Init stored)
           | Uninit -> raise Load_from_uninit
           | Killed -> raise Not_sequentialisable)
      | _ ->
        (* classify_action marks these cases as Use_other, which are filtered
         * out before this function is called. *)
        Some (Es.empty, env)
      end
  | Esseq (_, e1, e2) ->
      let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
      let* (ev2, env2) = sequentialisable seq_memo sym env1 e2 in
      Some (Es.union ev1 ev2, env2)
  | Ewseq (_, e1, e2) ->
      let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
      let* (ev2, env2) = sequentialisable seq_memo sym env1 e2 in
      if Es.exists Event.is_neg_store ev1
          && not (Es.is_empty ev2) then
        raise Not_sequentialisable
      else
        Some (Es.union ev1 ev2, env2)
  | Eif (pe, et, ef) ->
      let rt = sequentialisable seq_memo sym env et in
      let rf = sequentialisable seq_memo sym env ef in
      combine_branches pe rt rf
  | Ecase (pe, arms) ->
      let arm_results =
        List.map (fun (pat, e) -> (pat, sequentialisable seq_memo sym env e)) arms
      in
      combine_case_branches pe arm_results
  | End arms | Epar arms | Eunseq arms ->
      let eventful_arms = List.filter_map
        (fun arm ->
          let* (ev, env') = sequentialisable seq_memo sym env arm in
          if Es.is_empty ev then None else Some (ev, env'))
        arms in
      let all_reads =
        List.for_all (fun (ev, _) ->
            Es.for_all Event.is_load ev) eventful_arms in
      if all_reads then
        (* All arms only load; env is unchanged. *)
        Some (Es.singleton Event.Load, env)
      else
        (* At most one write/kill arm, with no other arm having events. *)
        begin match eventful_arms with
          | [(ev, env')] -> Some (ev, env')
          | []           -> assert false (* handled by all_reads = true *)
          | _ :: _ :: _  -> raise Not_sequentialisable
        end
  | Esave ((label_sym, _), params, _body) ->
      (match find_single_direct_alias sym
               (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
       | None           -> Some (Es.empty, env)
       | Some param_sym -> save_param_needs_init seq_memo sym env label_sym param_sym)
  | Erun (_, label_sym, args) ->
      let entry = Pmap.find label_sym seq_memo in
      (match find_single_direct_alias sym
               (List.combine (List.map fst entry.params) args) with
       | None           -> ()
       | Some param_sym ->
           ignore (save_param_needs_init seq_memo sym env label_sym param_sym));
      None
  | Elet (_, _, e) | Eannot (_, e) ->
      sequentialisable seq_memo sym env e
  | Ebound e ->
    let* (_, env) = sequentialisable seq_memo sym env e in
    Some (Es.empty, env)
  | Epure _ | Ememop _ | Eccall _ | Eproc _ | Ewait _ | Eexcluded _ ->
      Some (Es.empty, env)

(* save_param_needs_init seq_memo sym env label_sym param_sym:
   Analyses the Esave body for (label_sym, param_sym) w.r.t. sym and
   memoises the result.  Returns the body's sequentialisable result
   (None if all paths end in Erun).

   - Sentinel (false, None) is written before recursing so that back-edge
     Erun calls find the entry and do not loop.
   - If Load_from_uninit is raised (body reads sym before any store):
       * If outer env = Init _: mark init_needed=true, re-run with outer env.
       * Otherwise: re-raise Load_from_uninit.
   - If already memoised with init_needed=true and env ≠ Init _: re-raise
     Load_from_uninit. *)
and save_param_needs_init seq_memo sym env label_sym param_sym
    : (Event_set.t * env) option =
  let entry = Pmap.find label_sym seq_memo in
  match Pmap.lookup param_sym !(entry.results) with
  | Some (true, result) ->
      (match env with
       | Init _ -> result
       | _      -> raise Load_from_uninit)
  | Some (false, result) ->
      result
  | None ->
      entry.results := Pmap.add param_sym (false, None) !(entry.results);
      (try
        let result = sequentialisable seq_memo param_sym Uninit entry.body in
        entry.results := Pmap.add param_sym (false, result) !(entry.results);
        result
      with Load_from_uninit ->
        match env with
        | Init _ ->
            let result = sequentialisable seq_memo param_sym env entry.body in
            entry.results := Pmap.add param_sym (true, result) !(entry.results);
            result
        | _ -> raise Load_from_uninit)

(* ------------------------------------------------------------------ *)
(* Promotability analysis for a single procedure                       *)
(* ------------------------------------------------------------------ *)

let find_promotable ~also_fun_args f_sym body : Symbol.sym list =
  let use_memo  : use list memo_save_info = collect_esave_defs body in
  let seq_memo  : seq_memo =
    Pmap.map (fun { params; body; _ } ->
      { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) use_memo in
  let creates = collect_creates ~also_fun_args body in
  let is_promotable s =
    List.for_all addr_not_taken (collect_uses use_memo s body)
    && (match sequentialisable seq_memo s Uninit body with
        | None | Some _ -> true
        | exception Not_sequentialisable -> false
        | exception Load_from_uninit    -> false)
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
