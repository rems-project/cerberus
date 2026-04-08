(* This file implements an analysis to find 'promotable' variables,
   stack variables which can be promoted out of memory operations and
   into pure Core expressions. *)
open Core

let is_pesym sym (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Symbol.symbolEquality s sym
  | _ -> false

let sym_empty_set = Pset.empty Symbol.compare_sym

let sym_empty_map = Pmap.empty Symbol.compare_sym

(* [pe_free_syms pe] is the set of all (free) symbols mentioned in [pe]
   The pointer syms we care about are always bound in effectful expressions,
   hence we can skip tracking variables bound inside [pe] *)
let rec pe_free_syms (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Pset.singleton Symbol.compare_sym s
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ -> sym_empty_set
  | PEctor (_, pes) | PEcall (_, pes) | PEmemop (_, pes) ->
      pes_free_syms pes
  | PEcase (pe, arms) ->
      pes_free_syms (pe :: (List.map snd arms))
  | PEarray_shift (pe1, _, pe2) | PEop (_, pe1, pe2)
  | PElet (_, pe1, pe2) | PEwrapI (_, _, pe1, pe2)
  | PEcatch_exceptional_condition (_, _, pe1, pe2)
  | PEare_compatible (pe1, pe2) ->
      pes_free_syms [pe1; pe2]
  | PEmember_shift (pe, _, _)
  | PEconv_int (_, pe)
  | PEnot pe
  | PEis_scalar pe | PEis_integer pe | PEis_signed pe | PEis_unsigned pe
  | PEmemberof (_, _, pe) | PEunion (_, _, pe) | PEcfunction pe
  | PEbmc_assume pe ->
      pe_free_syms pe
  | PEif (pe1, pe2, pe3) ->
      pes_free_syms [pe1; pe2; pe3]
  | PEconstrained ivs ->
      pes_free_syms (List.map snd ivs)
  | PEstruct (_, fields) ->
      pes_free_syms (List.map snd fields)

and pes_free_syms pes =
  List.fold_left (fun set pe ->
      Pset.union set (pe_free_syms pe)) sym_empty_set pes

(* [action_escaping_syms creates act_] is the set of all vars which are
   mentioned in non-direct-address positions. For Store0/Load0/Kill/SeqRMW the
   bare-PEsym address argument is excluded; everything else is included.  *)
let action_escaping_syms act_ =
  (* addr_indirect addr_pe: if not a bare PEsym, all syms in addr_pe are bad *)
  let addr_indirect addr_pe =
    match addr_pe with
    | Pexpr (_, _, PEsym _) ->
      sym_empty_set
    | _ ->
      pe_free_syms addr_pe
  in
  match act_ with
  | Store0 (_, ctype_pe, addr_pe, val_pe, _) ->
      Pset.union (addr_indirect addr_pe) (pes_free_syms [ctype_pe; val_pe])
  | Load0 (_, addr_pe, _) | Kill (_, addr_pe) ->
      addr_indirect addr_pe
  | SeqRMW (_, ty_pe, addr_pe, _, upd_pe) ->
      Pset.union (addr_indirect addr_pe) (pes_free_syms [ty_pe; upd_pe])
  | Create (pe1, pe2, _) | Alloc0 (pe1, pe2, _)
  | LinuxLoad (pe1, pe2, _) ->
      pes_free_syms [pe1; pe2]
  | CreateReadOnly (pe1, pe2, pe3, _) | LinuxStore (pe1, pe2, pe3, _)
  | LinuxRMW (pe1, pe2, pe3, _) ->
      pes_free_syms [pe1; pe2; pe3]
  | Fence0 _ | LinuxFence _ -> sym_empty_set
  | RMW0 (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeStrong (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeWeak (pe1, pe2, pe3, pe4, _, _) ->
      pes_free_syms [pe1; pe2; pe3; pe4]

(* ------------------------------------------------------------------ *)
(* Esave memo tables                                                  *)
(*                                                                    *)
(* sequentialisable analyses Esave bodies once via the default args   *)
(* and once per Erun call site.  Results are memoised per             *)
(* (label_sym, param_sym) to avoid redundant traversals and to        *)
(* terminate on back-edge Eruns.                                      *)
(* ------------------------------------------------------------------ *)

type 'a esave_memo_entry = {
  params  : (Symbol.sym * pexpr) list;            (* (param_sym, default_pe) by position *)
  body    : (unit, unit, Symbol.sym) generic_expr;
  results : (Symbol.sym, 'a) Pmap.map ref;        (* param_sym -> cached result, filled lazily *)
}

type escaped =
  | Not_escaped
  | Escaped

(* Erun arguments, and default arguments to Esave are handled specially: if
   an argument is a bare PEsym AND the corresponding parameter is NOT escaped
   in the Esave body, then it's considered NOT escaped. *)
let run_escaping_syms args params results =
  let is_pesym = function
    | Pexpr (_, _, PEsym _) -> true
    | _ -> false in
  let is_escaped param =
    (* [Pmap.find] throws [Not_found] (if the code is wrong) which gets
       picked up by a handler in the parsers/c/c_lexer.mll of all places,
       and the resulting backtrace is confusing *)
    match Option.get @@ Pmap.lookup param results with
      | Escaped -> true
      | Not_escaped -> false in
  List.fold_left2
    (fun escaped param arg ->
      if not (is_pesym arg) || is_escaped param then
        Pset.union escaped (pe_free_syms arg)
      else
        escaped)
    sym_empty_set
    params
    args

let mark_set status set map =
  Pset.fold (fun sym map ->
      if Pmap.mem sym map then
        Pmap.add sym status map
      else
        map) set map

(* Single pass over an expression that simultaneously
   (a) collects all Esave definitions into a memo table,
   (b) collects Create-bound syms that are candidates for promotion, and
   (c) removes from the candidate set any sym that appears in a non-direct-
       address position (i.e., not as the bare PEsym address argument of a
       Store0/Load0/Kill/SeqRMW). Whatever remains in [create_syms] after the
       walk has been seen only in those safe positions.

   Note that symbols are NOT unique per binder: a pointer to a C local object
   will have the same symbol, regardless of how many times it is bound (in an
   Esave, or across different Creates/lifetimes). This means the analysis needs
   to actually be flow-insenstive (e.g. ignore that control does not return
   after an Erun) to be correct: a symbol is promotable if ALL its lifetimes do
   not escape its address. *)
let rec collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) (Expr (annots, e_)) =
  match e_ with
  | Esave ((label_sym, _), params, body) ->
      (* There's some subtlety around this case.
         1. Not all Esave params are pointers - the elaboration for a "return"
            will have one parameter whose type corresponds to that of the C
            function's return type (which can be a pointer itself, and thus
            be a valid route of escaping!).
         2. The binder/parameter for a C local object re-uses THE SAME SYMBOL as
            the one binding the create.
         This makes calculating whether the _parameter_ escapes by itself
         in the body more fiddly: after recursing we have to patch up the
         map of pointers. *)
      let params = List.map (fun (s, (_, pe)) -> (s, pe)) params in
      let (param_syms, def_args) = List.split params in
      (* Unconditionally add the param syms for analysis in the body.
         Note that for a return label, this adds the return value parameter
         unconditionally regardless of whether it's a pointer or not. *)
      let with_params = List.fold_left (fun map sym ->
          Pmap.add sym Not_escaped map) create_syms param_syms in
      let (esave_memo, post_body_with_params, pending_eruns) =
          collect_info
            ~also_fun_args
            (esave_memo, with_params, pending_eruns)
            body in
      (* The results of whether the label parameter escapes are cached
         for checking the default arguments and runs to that label. *)
      let results =
        ref @@
        List.fold_left (fun results sym ->
            let status = Option.get @@ Pmap.lookup sym post_body_with_params in
            Pmap.add sym status results)
          sym_empty_map
          param_syms in
      let esave_memo = Pmap.add label_sym { params; body; results } esave_memo in
      (* If a param_sym had been
         - Not_escaped before, but Escaped in the body, or
         - Escaped before, but Not_escaped in the body, or
         - a return value parameter
         then map needs to be reset to what it was (including removing the
         return value parameter). However, new syms (creates within the body)
         need to be preserved.

         Because the symbols for C local objects are re-used, such param syms
         are guaranteed to be in the original create_syms map, which must then
         be reset to its original value (before analysing its use via default
         arguments). If a param sym is not the original create_syms map, then
         it's a return param sym which must be removed. *)
      let post_body_no_params =
        List.fold_left (fun map sym ->
            match Pmap.lookup sym create_syms with
            | None -> Pmap.remove sym map
            | Some status -> Pmap.add sym status map)
          post_body_with_params
          param_syms in
      (* Now that we've computed whether the parameters are escaped by the
         body, we can check the default arguments don't escape a pointer,
         either directly or via its corresponding parameter. *)
      let arg_escaped = run_escaping_syms def_args param_syms !results in
      let create_syms = mark_set Escaped arg_escaped post_body_no_params in
      (esave_memo, create_syms, pending_eruns)
  | Esseq (
      Pattern (_, CaseBase (Some sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _,
          (Symbol.PrefSource _ | Symbol.PrefCompoundLiteral _)))))),
      body
    ) ->
      let create_syms =
        (* Symbols are re-used across different lifetimes, so need to
           be careful to not override information of prior ones. *)
        if not (Pmap.mem sym create_syms) then
            Pmap.add sym Not_escaped create_syms
        else
          create_syms
      in
      collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) body
  | Esseq (
      Pattern (_, CaseBase (Some sym, _)),
      Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefFunArg _))))),
      body
    ) when also_fun_args ->
      let create_syms =
        (* Symbols are re-used across different lifetimes, so need to
           be careful to not override information of prior ones. *)
        if not (Pmap.mem sym create_syms) then
            Pmap.add sym Not_escaped create_syms
        else
          create_syms
      in
      collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) body
  | Eaction (Paction (_, Action (_, _, act_))) ->
      (esave_memo, mark_set Escaped (action_escaping_syms act_) create_syms, pending_eruns)
  | Epure pe ->
      (esave_memo, mark_set Escaped (pe_free_syms pe) create_syms, pending_eruns)
  | Ememop (_, pes) ->
      (esave_memo, mark_set Escaped (pes_free_syms pes) create_syms, pending_eruns)
  | Elet (_, pe, e) ->
      let create_syms = mark_set Escaped (pe_free_syms pe) create_syms in
      collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) e
  | Ecase (pe, arms) ->
      collect_info_list
        ~also_fun_args
        (esave_memo, mark_set Escaped (pe_free_syms pe) create_syms, pending_eruns)
        (List.map snd arms)
  | Eif (pe, e1, e2) ->
      collect_info_list
        ~also_fun_args
        (esave_memo, mark_set Escaped (pe_free_syms pe) create_syms, pending_eruns)
        [e1; e2]
  | Eccall (_, fn_pe, arg_pe, pes) ->
      let create_syms = mark_set Escaped (pes_free_syms ([fn_pe; arg_pe] @ pes)) create_syms in
      (esave_memo, create_syms, pending_eruns)
  | Eproc (_, _, pes) ->
      (esave_memo, mark_set Escaped (pes_free_syms pes) create_syms, pending_eruns)
  | Erun (_, label_sym, args) ->
      (match Pmap.lookup label_sym esave_memo with
        | Some { params; body = _; results } ->
          let escaped_syms = run_escaping_syms args (List.map fst params) !results in
          (esave_memo, mark_set Escaped escaped_syms create_syms, pending_eruns)
      | None ->
        (esave_memo, create_syms, (label_sym, args) :: pending_eruns))
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
    collect_info_list
      ~also_fun_args
      (esave_memo, create_syms, pending_eruns)
      [e1; e2]
  | Ebound e | Eannot (_, e) ->
    collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) e
  | Eunseq es | End es | Epar es ->
    collect_info_list
      ~also_fun_args
      (esave_memo, create_syms, pending_eruns)
      es
  | Ewait _ | Eexcluded _ ->
    (esave_memo, create_syms, pending_eruns)

and collect_info_list ~also_fun_args (esave_memo, create_syms, pending_eruns) es =
  List.fold_left (fun (esave_memo, create_syms, pending_eruns) e ->
      collect_info ~also_fun_args (esave_memo, create_syms, pending_eruns) e)
    (esave_memo, create_syms, pending_eruns)
    es

let collect_info ~also_fun_args body =
  let (esave_memo, create_syms, pending_eruns) =
    collect_info ~also_fun_args (sym_empty_map, sym_empty_map, []) body
  in
  let create_syms =
    List.fold_left (fun create_syms (label_sym, args) ->
        let { params; body = _; results } =
          (* [Pmap.find] throws [Not_found] (if the code is wrong) which gets
             picked up by a handler in the parsers/c/c_lexer.mll of all places,
             and the resulting backtrace is confusing *)
          Option.get @@ Pmap.lookup label_sym esave_memo in
        let escaped_syms = run_escaping_syms args (List.map fst params) !results in
        mark_set Escaped escaped_syms create_syms)
      create_syms
      pending_eruns in
  (esave_memo, create_syms)

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
(* Init        — sym was last stored with committed value pe          *)
(* Killed      — sym's allocation was freed                           *)
type env = Uninit | Init | Killed
let is_uninit = function Uninit -> true | _ -> false
let is_killed = function Killed -> true | _ -> false
let is_init   = function Init   -> true | _ -> false

exception Not_sequentialisable
exception Load_from_uninit

(* merges sequentialisable results from Eif/Ecase arms if they all agree
 * Note: this is fine for transforming too because we can use PEundef
 * as values for non-returning branches *)
let combine_branches arm_results =
  let branches = List.filter_map Fun.id arm_results in
  let all_evs, all_env = List.split branches in
  let all_evs = List.fold_left Event_set.union Event_set.empty all_evs in
  let combined_env =
    if List.for_all is_uninit all_env then
      Uninit
    else if List.for_all is_killed all_env then
      Killed
    else if List.for_all is_init all_env then
       Init
    else
       raise Not_sequentialisable in
  (all_evs, combined_env)

let is_init_env needs_init ~param_env ~env =
  if needs_init then
    (match env with
    | Killed -> raise Not_sequentialisable
    | Uninit -> raise Load_from_uninit
    | Init -> param_env)
  else
    (match param_env with
     | Uninit -> env            (* body didn't alter sym; outer state persists *)
     | Init | Killed -> param_env)

type 'a memo_save_info = (Symbol.sym, 'a esave_memo_entry) Pmap.map

(* seq_memo: memoises sequentialisable results per (label_sym, param_sym).
   'a = bool * (Event_set.t * env) option
     fst = init_needed: body requires Init env on entry (true) or
           self-initialises (false)
     snd = None while in progress or all paths end in Erun;
           Some (ev, env') otherwise *)

type seq_memo = (bool * (Event_set.t * env) option) memo_save_info

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

let rec sequentialisable (seq_memo : seq_memo) sym env (Expr (_, e_))
    : (Event_set.t * env) option =
  let module Es = Event_set in
  let ( let* ) = Option.bind in
  let must_return = function
    | None -> raise Not_sequentialisable
    | Some (ev, env) -> (ev, env) in
  match e_ with
  | Eaction (Paction (polarity, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, val_pe, _) when is_pesym sym addr_pe ->
          let ev = match polarity with
            | Pos -> Event.Pos_store
            | Neg -> Event.Neg_store in
        Some (Es.singleton ev, Init)
      | Load0 (_, addr_pe, _) when is_pesym sym addr_pe ->
          (match env with
           | Init   -> Some (Es.singleton Event.Load, env)
           | Uninit  -> raise Load_from_uninit
           | Killed  -> raise Not_sequentialisable)
      | Kill (_, addr_pe) when is_pesym sym addr_pe ->
          Some (Es.singleton Event.Kill, Killed)
      | SeqRMW (_, _, addr_pe, tmp_sym, upd_pe) when is_pesym sym addr_pe ->
          (match env with
           | Init -> Some (Es.of_list [Event.Load; Event.Pos_store], Init)
           | Uninit -> raise Load_from_uninit
           | Killed -> raise Not_sequentialisable)
      | _ ->
        (* sym was verified to appear only as a direct address argument
         * (collect_info left it in creates), so non-address actions are
         * irrelevant and can be skipped. *)
        Some (Es.empty, env)
      end
  | Esseq (_, e1, e2) ->
      let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
      let* (ev2, env2) = sequentialisable seq_memo sym env1 e2 in
      Some (Es.union ev1 ev2, env2)
  | Ewseq (_, e1, e2) ->
      (* race-condition analysis is invalid if e1/e2 don't return
       * or, assume definite race if either expression doesn't return *)
    let (ev1, env1) = must_return @@ sequentialisable seq_memo sym env e1 in
    let (ev2, env2) = must_return @@ sequentialisable seq_memo sym env1 e2 in
    if Es.exists Event.is_neg_store ev1
        && not (Es.is_empty ev2) then
      raise Not_sequentialisable
    else
      Some (Es.union ev1 ev2, env2)
  | Eif (pe, et, ef) ->
      let rt = sequentialisable seq_memo sym env et in
      let rf = sequentialisable seq_memo sym env ef in
      Some (combine_branches [rt; rf])
  | Ecase (pe, arms) ->
      let arm_results =
        List.map (fun (_, e) -> sequentialisable seq_memo sym env e) arms
      in
      Some (combine_branches arm_results)
  | End arms | Epar arms | Eunseq arms ->
      let eventful_arms = List.filter_map
        (fun arm ->
          (* race-condition analysis is invalid if e1/e2 don't return or,
           * assume definite race if either expression doesn't return *)
          let (ev, env') = must_return @@ sequentialisable seq_memo sym env arm in
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
       | Some param_sym ->
         let (needs_init, result) =
             save_param_needs_init seq_memo sym label_sym param_sym in
         let* (ev, param_env) = result in
         Some (ev, is_init_env needs_init ~env ~param_env))
  | Erun (_, label_sym, args) ->
      (* [Pmap.find] throws [Not_found] (if the code is wrong) which gets
         picked up by a handler in the parsers/c/c_lexer.mll of all places,
         and the resulting backtrace is confusing *)
      let entry = Option.get @@ Pmap.lookup label_sym seq_memo in
      (match find_single_direct_alias sym
               (List.combine (List.map fst entry.params) args) with
       | None           -> ()
       | Some param_sym ->
         let (needs_init, result) =
           save_param_needs_init seq_memo sym label_sym param_sym in
         Option.iter (fun (ev, param_env) ->
             ignore (is_init_env needs_init ~env ~param_env))
           result);
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
       * If outer env = Init: mark init_needed=true, re-run with outer env.
       * Otherwise: re-raise Load_from_uninit.
   - If already memoised with init_needed=true and env ≠ Init: re-raise
     Load_from_uninit. *)
and save_param_needs_init seq_memo sym label_sym param_sym
    : bool * (Event_set.t * env) option =
  (* [Pmap.find] throws [Not_found] (if the code is wrong) which gets
     picked up by a handler in the parsers/c/c_lexer.mll of all places,
     and the resulting backtrace is confusing *)
  let entry = Option.get @@ Pmap.lookup label_sym seq_memo in
  match Pmap.lookup param_sym !(entry.results) with
  | Some result -> result
  | None ->
      entry.results := Pmap.add param_sym (false, None) !(entry.results);
      (try
        let result = sequentialisable seq_memo param_sym Uninit entry.body in
        entry.results := Pmap.add param_sym (false, result) !(entry.results);
        (false, result)
      with Load_from_uninit ->
        let result = sequentialisable seq_memo param_sym Init entry.body in
        entry.results := Pmap.add param_sym (true, result) !(entry.results);
        (true, result))

(* ------------------------------------------------------------------ *)
(* Promotability analysis for a single procedure                       *)
(* ------------------------------------------------------------------ *)

let find_promotable ~also_fun_args f_sym body : Symbol.sym list =
  let esave_memo, creates = collect_info ~also_fun_args body in
  let seq_memo  : seq_memo =
    Pmap.map (fun { params; body; _ } ->
      { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) esave_memo in
  let is_promotable s =
    match sequentialisable seq_memo s Uninit body with
    | None | Some _ -> true
    | exception Not_sequentialisable -> false
    | exception Load_from_uninit    -> false
  in
  let (not_esc, _) =
    Pmap.partition
      (fun _ -> function Not_escaped -> true | Escaped -> false)
      creates in
  let promotable = List.filter is_promotable (Pset.elements @@ Pmap.domain not_esc) in
  Cerb_debug.print_debug 3 [] (fun () ->
    Printf.sprintf "[mem2reg] %s: %d promotable: [%s]"
      (Pp_symbol.to_string_pretty f_sym)
      (List.length promotable)
      (String.concat ", " (List.map Pp_symbol.to_string promotable)));
  promotable

(* ------------------------------------------------------------------ *)
(* transform_file: analysis phase only — file returned unchanged       *)
(* ------------------------------------------------------------------ *)

let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  let funs = Pmap.mapi (fun f_sym decl ->
    match decl with
    | Proc (loc, env_marker, ret_bt, args, body, _) ->
        let promotable = find_promotable ~also_fun_args f_sym body in
        Proc (loc, env_marker, ret_bt, args, body, promotable)
    | Fun _ | ProcDecl _ | BuiltinDecl _ ->
        decl) file.funs in
  { file with funs }
