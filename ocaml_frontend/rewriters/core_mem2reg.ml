(* This file implements an analysis to find 'promotable' variables,
   stack variables which can be promoted out of memory operations and
   into pure Core expressions. *)
open Core

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

type 'a collect_saves_entry = {
  params  : (Symbol.sym * pexpr) list;
  body    : (unit, unit, Symbol.sym) generic_expr;
  results : (Symbol.sym, 'a) Pmap.map;
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
      let arg_escaped = run_escaping_syms def_args param_syms results in
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
          let escaped_syms = run_escaping_syms args (List.map fst params) results in
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
  | Eunseq es | Epar es ->
    collect_info_list
      ~also_fun_args
      (esave_memo, create_syms, pending_eruns)
      es
  | End _ (* always true/false *) | Ewait _ | Eexcluded _ ->
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
        let escaped_syms = run_escaping_syms args (List.map fst params) results in
        mark_set Escaped escaped_syms create_syms)
      create_syms
      pending_eruns in
  create_syms

let pesym_mem (Pexpr (_, _, pe_)) set =
  match pe_ with
  | PEsym s -> Pset.mem s set
  | _ -> false

let get_sym (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> s
  | _ -> assert false

let update_syms syms footprint =
  Pmap.fold (fun sym f syms ->
      match f with
      | Ok _ ->
          Pset.add sym syms
      | Error _ ->
          Pset.remove sym syms)
    footprint
    syms

module Event = struct
  type t = Neg_store | Pos_store | Load
  let is_neg_store = function Neg_store -> true | _ -> false
  let is_load = function Load -> true | _ -> false
  let compare x y =
    let num = function
    | Neg_store -> 0
    | Pos_store -> 1
    | Load -> 2 in
    Int.compare (num x) (num y)

  let _to_string = function
    | Neg_store -> "N"
    | Pos_store -> "P"
    | Load -> "O"
end

module Event_set = Set.Make(Event)

let opt_lift2 f x y =
  match x, y with
  | None, None -> None
  | Some _ as s, None | None, (Some _ as s) -> s
  | Some x, Some y -> Some (f x y)

let res_lift2 f x y =
  Result.bind x (fun x ->
      Result.bind y (fun y ->
          Ok (f x y)))

let combine_map f =
  Pmap.merge (Fun.const (opt_lift2 f))

let union_footprint = function
    | [] -> assert false
    | m :: ms ->
      List.fold_left (combine_map (res_lift2 Event_set.union)) m ms

(* [sequence syms e] returns a map whose keys are a subset of [syms] touched by
   [e]. The values of the map are either error, signalling that the symbol is
   not sequentialisable, or an event set of memory events. *)
let rec sequence syms (Expr (annots, e_) as _e) =
  let module Es = Event_set in
  match e_ with
  | Eaction (Paction (polarity, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, val_pe, _)
        when pesym_mem addr_pe syms ->
          Pmap.add
            (get_sym addr_pe)
            (let ev = match polarity with
                | Pos -> Event.Pos_store
                | Neg -> Event.Neg_store in
             Ok (Es.singleton ev))
            sym_empty_map
      | Load0 (_, addr_pe, _)
        when pesym_mem addr_pe syms ->
          Pmap.add
            (get_sym addr_pe)
            (Ok (Es.singleton Event.Load))
             sym_empty_map
      | SeqRMW (_, _, addr_pe, _, _)
        when pesym_mem addr_pe syms ->
          Pmap.add
            (get_sym addr_pe)
            (Ok (Es.of_list [Event.Pos_store; Event.Load]))
             sym_empty_map
      | _ ->
          sym_empty_map
      end

  | Esseq (_, e1, e2) ->
      let footprint1 = sequence syms e1 in
      let syms1 = update_syms syms footprint1 in
      let footprint2 = sequence syms1 e2 in
      union_footprint [footprint1; footprint2]

  | Ewseq (_, e1, e2) ->
      let footprint1 = sequence syms e1 in
      let syms1 = update_syms syms footprint1 in
      let footprint2 = sequence syms1 e2 in
      let union_if_no_race ev1 ev2 =
        let ( let* ) = Result.bind in
        let* ev1 in
        let* ev2 in
        if Es.exists Event.is_neg_store ev1 && not (Es.is_empty ev2) then
          Error ()
        else
          Ok (Es.union ev1 ev2) in
      combine_map union_if_no_race footprint1 footprint2

  | Epure _ | Ememop _ | Eccall _ | Eproc _ | Ewait _ | Eexcluded _
  | End _ (* always true/false *) ->
      sym_empty_map

  | Elet (_, _, e) | Eannot (_, e) ->
      sequence syms e

  | Ebound e ->
      Pmap.map (Result.map (fun _ -> Es.empty)) @@
      sequence syms e

  | Eif (_, e1, e2) ->
      union_footprint @@ List.map (sequence syms) [e1; e2]

  | Ecase (_, arms) ->
      union_footprint @@ List.map (fun (_, e) -> sequence syms e) arms

  | Epar arms | Eunseq arms ->
      arms
      |> List.map (sequence syms)
      |> List.map (Pmap.map (Result.map (fun x -> [x])))
      |> List.fold_left (combine_map (res_lift2 List.append)) (sym_empty_map)
      |> Pmap.map (fun fs ->
          Result.bind fs (fun fs ->
              let eventful = List.filter (fun s -> not (Es.is_empty s)) fs in
              let all_reads =
                List.for_all (Es.for_all Event.is_load) eventful in
              if all_reads then
                Ok (Es.singleton Event.Load)
              else
                begin match eventful with
                  | [ev] -> Ok ev
                  | [] -> assert false (* handled by all_reads = true *)
                  | _ :: _ :: _ -> Error ()
                end))

  | Esave (_, params, body) ->
      (* This relies on the fact that
           1. C local var symbols are re-used across Esave-parameters,
              Esave arguments, and Erun arguments.
           2. [collect_info] ensures that the arguments are plain symbols.
         This means we can
           1. Ignore any parameter which is not in [syms].
           2. Conflate the parameter symbols of the Esave, with the default
              arguments of the Esave (for non-return Esaves).
         NOTE: For return Esaves, since the body is always a pure expression,
         the return parameter symbol will not end up in the footprint. *)
      let params = List.filter_map (fun (sym, _) ->
        if Pset.mem sym syms then Some sym else None) params in
      let param_syms = Pset.union syms (Pset.from_list Symbol.compare_sym params) in
      sequence param_syms body

  | Erun (_, label_sym, args) ->
      (* This relies on the fact that
           1. C local var symbols are re-used across Esave-parameters.
           2. [collect_info] ensures that the arguments are plain symbols.
         This means we can conflate the parameter symbols of the Esave,
         with the arguments of the Erun.
         Because control does not return from an Erun, we don't care
         about the footprint of sequence-able symbols.
         And because the symbols are conflated, any non-sequence-able
         symbols will be caught by the Esave analysis. *)
      sym_empty_map

let find_promotable ~also_fun_args f_sym body : Symbol.sym list =
  let creates = collect_info ~also_fun_args body in
  let not_esc =
    Pmap.domain @@
    Pmap.filter
      (fun _ -> function Not_escaped -> true | Escaped -> false)
      creates in
  let not_seq =
      Pmap.domain @@
      Pmap.filter
        (fun _ -> function Error _ -> true | (Ok _) -> false)
        (sequence not_esc body) in
  assert (Pset.subset not_seq not_esc);
  (* The usual elaboration ensures that all C local var symbols are written to
     at least once, but not for the CN backend. This means that totally unused
     C local vars would have no footprint and not show up in the domain of the
     syms mapped to [Ok _]. Hence starting with not-escaped vars and removing
     not-sequence-able ones instead. *)
  let promotable = Pset.elements (Pset.diff not_esc not_seq) in
  Cerb_debug.print_debug 3 [] (fun () ->
    Printf.sprintf "[mem2reg] %s: %d promotable: [%s]"
      (Pp_symbol.to_string_pretty f_sym)
      (List.length promotable)
      (String.concat ", " (List.map Pp_symbol.to_string promotable)));
  promotable

let get_ct (Pexpr (_, _, e_)) =
  match e_ with
  | PEval (Vctype ct) -> ct
  | _ -> assert false

let is_unit_pat (Pattern (_, pat_)) =
  match pat_ with
  | CaseBase (None, BTy_unit) -> true
  | _ -> false

let is_unit_pe (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEval Vunit -> true
  | _ -> false

let extend_pat bty_env to_bind pat =
  Cerb_debug.print_debug 3 [] (fun () ->
      let to_bind = Pset.elements to_bind |> List.map Pp_symbol.to_string in
      let dom = Pmap.domain bty_env |> Pset.elements |> List.map Pp_symbol.to_string in
      "[mem2reg-bind] " ^ (String.concat "," to_bind) ^ "\n" ^
      "[mem2reg-domn] " ^ (String.concat "," dom)
  );
  let new_sym sym =
    let str = Pp_symbol.to_string sym in
    let parts = String.split_on_char '_' str in
    Symbol.fresh_pretty (List.hd parts) in
  let Pattern (p_annots, pat_) = pat in
  let matched = Pset.elements to_bind |> List.map (fun x -> (x, new_sym x)) in
  let binders = List.map (fun (sym, new_sym) ->
      let bty = Option.get @@ Pmap.lookup sym bty_env in
      (* let bty = BTy_storable in *)
      Pattern ([], CaseBase (Some new_sym, bty))) matched in
  if List.is_empty binders then
    (matched, pat)
  else if is_unit_pat pat then
    (matched, Pattern ([], CaseCtor (Ctuple, binders)))
  else
    (matched, Pattern ([], CaseCtor (Ctuple, binders @ [pat])))

(*
type 'a nested =
  | Base of 'a
  | Tuple of 'a nested list

let rec nested_pat bty_env to_bind pat =
  match to_bind, pat with
  | Base to_bind, _ -> [extend_pat bty_env to_bind pat]
  | Tuple nested, Pattern ([], CaseCtor (Ctuple, pat)) ->
    List.concat @@ List.map2 (nested_pat bty_env) nested pat
  | _, _ -> assert false

let extend_pat bty_env to_bind pat =
  let pats = nested_pat bty_env to_bind pat in
  let (matched, pat) = List.fold_right (fun (m, p) (ms, ps) -> (m @ ms, p :: ps)) pats ([], []) in
  (matched, Pattern ([], CaseCtor (Ctuple, pat)))

let rec union_nested = function
  | Base to_bind -> to_bind
  | Tuple nested ->
    List.fold_left Pset.union sym_empty_set (List.map union_nested nested)
*)

let extend_pe pe env written =
  let pes = Pset.elements written |> List.map (fun sym -> Option.get @@ Pmap.lookup sym env) in
  if List.is_empty pes then
    Epure pe
  else if is_unit_pe pe then
    Epure (Pexpr ([], (), PEctor (Ctuple, pes)))
  else
    Epure (Pexpr ([], (), PEctor (Ctuple, pes @ [pe])))

let update_env env matched =
  List.fold_left (fun env (old, new_) ->
      let pe = Pexpr ([], (), PEsym new_) in
      Pmap.add old pe env) env matched

let transform_fun syms e =
  let cbt_to_bty x = BTy_loaded (Option.get @@ Core_aux.core_object_type_of_ctype x) in
  let bty_env = ref sym_empty_map in
  let rec transform val_env written (Expr (e_annot, e_)) =
    match e_ with
    | Esave ((label_sym, cbt), params, body) ->
      let is_return =
        List.exists (function Annot.Alabel LAreturn -> true | _ -> false) e_annot in
      if is_return then
        (Expr (e_annot, Esave ((label_sym, cbt), params, body)), sym_empty_set)
      else
        let sub_arg (sym, (info, arg)) =
          match Pmap.lookup sym val_env with
          | None -> (sym, (info, arg))
          | Some arg -> (sym, (info, arg)) in
        let (body, to_bind) = transform val_env written body in
        (Expr (e_annot, Esave ((label_sym, cbt), List.map sub_arg params, body)), to_bind)

    | Esseq (
        Pattern (_, CaseBase (Some sym, _)),
        Expr (e_annot, Eaction (Paction (_, Action (_, _, Create (_, ct, _))))),
        body
      ) ->
        let val_env =
          if Pset.mem sym syms then
            let ct = get_ct ct in
            let peval = Pexpr ([], (), PEval (Vloaded (LVunspecified ct))) in
            bty_env := Pmap.add sym (cbt_to_bty ct) !bty_env;
            Pmap.add sym peval val_env
          else
            val_env in
        transform val_env written body

    | Eaction (Paction (_, Action (_, _, act_))) ->
        begin match act_ with
        | Store0 (_, _, addr_pe, val_pe, _)
          when pesym_mem addr_pe syms ->
            let pe = Pexpr ([], (), PEctor (Ctuple, [val_pe])) in
            assert (Pmap.mem (get_sym addr_pe) !bty_env && Pmap.mem (get_sym addr_pe) val_env);
            let to_bind = (Pset.singleton Symbol.compare_sym (get_sym addr_pe)) in
            (Expr (e_annot, Epure pe), to_bind)

        | Load0 (_, addr_pe, _)
          when pesym_mem addr_pe syms ->
            let pexpr = Option.get @@ Pmap.lookup (get_sym addr_pe) val_env in
            (Expr (e_annot, Epure pexpr), sym_empty_set)

        | SeqRMW (_, _, addr_pe, x_sym, new_pe)
          when pesym_mem addr_pe syms ->
            let prev_pe = Option.get @@ Pmap.lookup (get_sym addr_pe) val_env in
            let new_pe = Core_aux.unsafe_subst_sym_pexpr x_sym prev_pe new_pe in
            assert (Pmap.mem (get_sym addr_pe) !bty_env && Pmap.mem (get_sym addr_pe) val_env);
            let to_bind = (Pset.singleton Symbol.compare_sym (get_sym addr_pe)) in
            (Expr (e_annot, Epure new_pe), to_bind)

        | Kill (_, addr_pe)
          when pesym_mem addr_pe syms ->
           (Expr (e_annot, Epure (Pexpr ([], (), PEval Vunit))), sym_empty_set)

        | _ ->
            (Expr (e_annot, e_), sym_empty_set)
        end

    | Epure pe ->
        (Expr (e_annot, extend_pe pe val_env written), written)

    | Elet (pat, pe, e) ->
        let (e, to_bind) = transform val_env written e in
        (Expr (e_annot, Elet (pat, pe, e)), to_bind)

    | Ecase (pe, arms) ->
        (* TODO *)
        (Expr (e_annot, e_), sym_empty_set)

    | Eunseq es | Epar es ->
        (* TODO *)
        (Expr (e_annot, e_), sym_empty_set)

    | Eif (pe, e1, e2) ->
        let (e1, to_bind1) = transform val_env written e1 in
        let unit_pat = Pattern ([], CaseBase (None, BTy_unit)) in
        let (matched1, pat1) = extend_pat !bty_env to_bind1 unit_pat in
        let env1 = update_env val_env matched1 in
        let (e2, to_bind2) = transform val_env written e2 in
        let (matched2, pat2) = extend_pat !bty_env to_bind2 unit_pat in
        let env2 = update_env val_env matched2 in
        let all_bound = Pset.union to_bind1 to_bind2 in
        let pe1 = extend_pe (Pexpr ([], (), PEval Vunit)) env1 all_bound in
        let pe2 = extend_pe (Pexpr ([], (), PEval Vunit)) env2 all_bound in
        let wrapped1 = Expr ([], Esseq (pat1, e1, Expr ([], pe1))) in
        let wrapped2 = Expr ([], Esseq (pat2, e2, Expr ([], pe2))) in
        (Expr (e_annot, Eif (pe, wrapped1, wrapped2)), all_bound)

    | Ememop _ | Eccall _ | Eproc _ | Ewait _ | Eexcluded _
    | End _ (* always true/false *) ->
        (Expr (e_annot, e_), sym_empty_set)

    | Erun (a, label_sym, args) ->
      let replace = function
        | Pexpr ([], (), PEsym sym) as arg ->
            (match Pmap.lookup sym val_env with
              | None -> arg
              | Some pe -> pe)
        | arg -> arg in
      (Expr (e_annot, Erun (a, label_sym, List.map replace args)), sym_empty_set)

    | Ewseq (pat, e1, e2) ->
       let (e1, to_bind) = transform val_env written e1 in
       let (matched, pat) = extend_pat !bty_env to_bind pat in
       let written = Pset.union to_bind written in
       let val_env = update_env val_env matched in
       let (e2, to_bind) = transform val_env written e2 in
       (Expr (e_annot, Ewseq (pat, e1, e2)), to_bind)

    | Esseq (pat, e1, e2) ->
       let (e1, to_bind) = transform val_env written e1 in
       let (matched, pat) = extend_pat !bty_env to_bind pat in
       let written = Pset.union to_bind written in
       let val_env = update_env val_env matched in
       let (e2, to_bind) = transform val_env written e2 in
       (Expr (e_annot, Esseq (pat, e1, e2)), to_bind)

    | Ebound e ->
        let (e, to_bind) = transform val_env written e in
        (Expr (e_annot, Ebound e), to_bind)

    | Eannot (a, e) ->
        let (e, to_bind) = transform val_env written e in
        (Expr (e_annot, Eannot (a, e)), to_bind)

  in
  transform sym_empty_map sym_empty_set e


let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  let funs = Pmap.mapi (fun f_sym decl ->
    match decl with
    | Proc (loc, env_marker, ret_bt, args, body, _) ->
        let promotable = find_promotable ~also_fun_args f_sym body in
        let (body, _) = transform_fun (Pset.from_list Symbol.compare_sym promotable) body in
        Proc (loc, env_marker, ret_bt, args, body, promotable)
    | Fun _ | ProcDecl _ | BuiltinDecl _ ->
        decl) file.funs in
  { file with funs }
