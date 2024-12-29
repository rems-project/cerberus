module BT = BaseTypes
module Res = Resource
module Req = Request
module LC = LogicalConstraints
module Loc = Locations
module IT = IndexTerms
module ITSet = Set.Make (IT)

type solver = Solver.solver

type s =
  { typing_context : Context.t;
    solver : solver option;
    sym_eqs : IT.t Sym.Map.t;
    past_models : (Solver.model_with_q * Context.t) list;
    found_equalities : EqTable.table;
    movable_indices : (Req.name * IT.t) list;
    unfold_resources_required : bool;
    log : Explain.log
  }

let empty_s (c : Context.t) =
  { typing_context = c;
    solver = None;
    sym_eqs = Sym.Map.empty;
    past_models = [];
    found_equalities = EqTable.empty;
    movable_indices = [];
    unfold_resources_required = false;
    log = []
  }


type 'a pause = ('a * s, TypeErrors.t) Result.t

type 'a t = s -> ('a * s, TypeErrors.t) Result.t

type 'a m = 'a t

type failure = Context.t * Explain.log -> TypeErrors.t

(* basic functions *)

let return (a : 'a) : 'a t = fun s -> Ok (a, s)

let fail (f : failure) : 'a t = fun s -> Error (f (s.typing_context, s.log))

let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
  fun s -> match m s with Error e -> Error e | Ok (x, s') -> (f x) s'


let ( let@ ) = bind

let get () : s t = fun s -> Ok (s, s)

(* due to solver interaction, this has to be used carefully *)
let set (s' : s) : unit t = fun _s -> Ok ((), s')

let run (c : Context.t) (m : 'a t) : 'a Or_TypeError.t =
  match m (empty_s c) with Ok (a, _) -> Ok a | Error e -> Error e


let run_to_pause (c : Context.t) (m : 'a t) : 'a pause =
  match m (empty_s c) with Ok (a, s) -> Ok (a, s) | Error e -> Error e


let run_from_pause (f : 'a -> 'b t) (pause : 'a pause) =
  match pause with Ok (a, s) -> Result.map fst @@ f a s | Error e -> Error e


let pause_to_result (pause : 'a pause) : 'a Or_TypeError.t = Result.map fst pause

let pure (m : 'a t) : 'a t =
  fun s ->
  Option.iter Solver.push s.solver;
  let outcome = match m s with Ok (a, _) -> Ok (a, s) | Error e -> Error e in
  Option.iter (fun s -> Solver.pop s 1) s.solver;
  outcome


let sandbox (m : 'a t) : 'a Or_TypeError.t t =
  fun s ->
  let n = Solver.num_scopes (Option.get s.solver) in
  Solver.push (Option.get s.solver);
  let outcome =
    match m s with
    | Ok (a, _s') ->
      assert (Solver.num_scopes (Option.get s.solver) = n + 1);
      Solver.pop (Option.get s.solver) 1;
      Ok a
    | Error e ->
      let n' = Solver.num_scopes (Option.get s.solver) in
      assert (n' > n);
      Solver.pop (Option.get s.solver) (n' - n);
      Error e
  in
  Ok (outcome, s)


let lift (m : 'a Or_TypeError.t) : 'a m =
  fun s -> match m with Ok r -> Ok (r, s) | Error e -> Error e


(* end basic functions *)

module Eff = Effectful.Make (struct
    type nonrec 'a t = 'a t

    let bind = bind

    let return = return
  end)

let iterM = Eff.ListM.iterM

(* functions to make values derived from the monad state *)

let make_simp_ctxt s =
  Simplify.
    { global = s.typing_context.global; values = s.sym_eqs; simp_hook = (fun _ -> None) }


let simp_ctxt () =
  let@ s = get () in
  return (make_simp_ctxt s)


let make_provable loc ({ typing_context = s; solver; _ } as c) =
  let simp_ctxt = make_simp_ctxt c in
  let f lc =
    Solver.provable
      ~loc
      ~solver:(Option.get solver)
      ~global:s.global
      ~assumptions:s.constraints
      ~simp_ctxt
      lc
  in
  f


let provable_internal loc =
  let@ s = get () in
  return (make_provable loc s)


(* boring functions for getting or setting, adding, or removing things in the context *)

let inspect (f : s -> 'a) : 'a t =
  let@ s = get () in
  return (f s)


let modify (f : s -> s) : unit t =
  let@ s = get () in
  set (f s)


let get_typing_context () : Context.t t = inspect (fun s -> s.typing_context)

let set_typing_context (c : Context.t) : unit t =
  modify (fun s -> { s with typing_context = c })


let inspect_typing_context (f : Context.t -> 'a) : 'a t =
  inspect (fun s -> f s.typing_context)


let modify_typing_context (f : Context.t -> Context.t) : unit t =
  let@ c = get_typing_context () in
  set_typing_context (f c)


let print_with_ctxt printer =
  let@ s = get_typing_context () in
  let () = printer s in
  return ()


let get_global () : Global.t t = inspect_typing_context (fun c -> c.global)

(** TODO delete this, have Global.t be constructed by itself *)
let set_global (g : Global.t) : unit t =
  modify_typing_context (fun s -> { s with global = g })


let record_action ((a : Explain.action), (loc : Loc.t)) : unit t =
  modify (fun s -> { s with log = Action (a, loc) :: s.log })


let modify_where (f : Where.t -> Where.t) : unit t =
  modify (fun s ->
    let log = Explain.State s.typing_context :: s.log in
    let typing_context = Context.modify_where f s.typing_context in
    { s with log; typing_context })


let get_member_type loc member layout : Sctypes.t m =
  let member_types = Memory.member_types layout in
  match List.assoc_opt Id.equal member member_types with
  | Some membertyp -> return membertyp
  | None ->
    fail (fun _ -> { loc; msg = Unexpected_member (List.map fst member_types, member) })


module ErrorReader = struct
  type nonrec 'a t = 'a t

  let return = return

  let bind = bind

  type state = s

  type global = Global.t

  let get = get

  let to_global (s : s) = s.typing_context.global

  let to_context (s : s) = s.typing_context

  let lift = lift
end

module Global = struct
  include Global.Lift (ErrorReader)

  let empty = Global.empty

  let is_fun_decl global id = Option.is_some @@ Global.get_fun_decl global id

  let get_logical_function_def_opt id = get_logical_function_def id

  let error_if_none opt loc msg =
    let@ opt in
    Option.fold
      opt
      ~some:return
      ~none:
        (let@ msg in
         fail (fun _ -> { loc; msg }))


  let get_logical_function_def loc id =
    error_if_none
      (get_logical_function_def id)
      loc
      (let@ res = get_resource_predicate_def id in
       return (TypeErrors.Unknown_logical_function { id; resource = Option.is_some res }))


  let get_struct_decl loc tag =
    error_if_none (get_struct_decl tag) loc (return (TypeErrors.Unknown_struct tag))


  let get_datatype loc tag =
    error_if_none (get_datatype tag) loc (return (TypeErrors.Unknown_datatype tag))


  let get_datatype_constr loc tag =
    error_if_none
      (get_datatype_constr tag)
      loc
      (return (TypeErrors.Unknown_datatype_constr tag))


  let get_struct_member_type loc tag member =
    let@ decl = get_struct_decl loc tag in
    let@ ty = get_member_type loc member decl in
    return ty


  let get_fun_decl loc fsym =
    error_if_none (get_fun_decl fsym) loc (return (TypeErrors.Unknown_function fsym))


  let get_lemma loc lsym =
    error_if_none (get_lemma lsym) loc (return (TypeErrors.Unknown_lemma lsym))


  let get_resource_predicate_def loc id =
    error_if_none
      (get_resource_predicate_def id)
      loc
      (let@ log = get_logical_function_def_opt id in
       return (TypeErrors.Unknown_resource_predicate { id; logical = Option.is_some log }))


  let get_fun_decls () =
    let@ global = get_global () in
    return (Sym.Map.bindings global.fun_decls)


  let add_struct_decl tag layout : unit m =
    let@ global = get_global () in
    set_global { global with struct_decls = Sym.Map.add tag layout global.struct_decls }


  let add_fun_decl fname entry =
    let@ global = get_global () in
    set_global { global with fun_decls = Sym.Map.add fname entry global.fun_decls }


  let add_lemma lemma_s (loc, lemma_typ) =
    let@ global = get_global () in
    set_global
      { global with lemmata = Sym.Map.add lemma_s (loc, lemma_typ) global.lemmata }


  let add_resource_predicate name entry =
    let@ global = get_global () in
    set_global
      { global with
        resource_predicates = Sym.Map.add name entry global.resource_predicates
      }


  let add_logical_function name entry =
    let@ global = get_global () in
    set_global
      { global with logical_functions = Sym.Map.add name entry global.logical_functions }


  let add_datatype name entry =
    let@ global = get_global () in
    set_global { global with datatypes = Sym.Map.add name entry global.datatypes }


  let add_datatype_constr name entry =
    let@ global = get_global () in
    set_global
      { global with datatype_constrs = Sym.Map.add name entry global.datatype_constrs }


  let set_datatype_order datatype_order =
    let@ g = get_global () in
    set_global { g with datatype_order }


  let get_datatype_order () =
    let@ g = get_global () in
    return g.datatype_order
end

(* end: convenient functions for global typing context *)

let add_sym_eqs sym_eqs =
  modify (fun s ->
    let sym_eqs =
      List.fold_left (fun acc (s, v) -> Sym.Map.add s v acc) s.sym_eqs sym_eqs
    in
    { s with sym_eqs })


let get_found_equalities () = inspect (fun s -> s.found_equalities)

let set_found_equalities eqs = modify (fun s -> { s with found_equalities = eqs })

let add_found_equalities lc =
  let@ eqs = get_found_equalities () in
  set_found_equalities (EqTable.add_lc_eqs eqs lc)


let get_past_models () = inspect (fun s -> s.past_models)

let set_past_models ms = modify (fun s -> { s with past_models = ms })

let drop_past_models () = set_past_models []

let bound_a sym = inspect_typing_context (fun s -> Context.bound_a sym s)

let bound_l sym = inspect_typing_context (fun s -> Context.bound_l sym s)

let bound sym = inspect_typing_context (fun s -> Context.bound sym s)

let get_a sym = inspect_typing_context (fun s -> Context.get_a sym s)

let get_l sym = inspect_typing_context (fun s -> Context.get_l sym s)

let add_a sym bt info = modify_typing_context (fun s -> Context.add_a sym bt info s)

let add_a_value sym value info =
  modify_typing_context (fun s -> Context.add_a_value sym value info s)


let add_l sym bt info = modify_typing_context (fun s -> Context.add_l sym bt info s)

let rec add_ls = function
  | [] -> return ()
  | (s, ls, info) :: lvars ->
    let@ () = add_l s ls info in
    add_ls lvars


let get_cs () = inspect_typing_context (fun c -> c.constraints)

let remove_a sym =
  let@ s = get_typing_context () in
  set_typing_context (Context.remove_a sym s)


let remove_as = iterM remove_a

(* let add_label_to_trace label =  *)
(*   modify_typing_context (fun c -> Context.add_label_to_trace label c) *)

(* let add_trace_item_to_trace i =  *)
(*   modify_typing_context (fun c -> Context.add_trace_item_to_trace i c) *)

(* similar but less boring functions, where components interact *)

let set_unfold_resources () =
  modify (fun s -> { s with unfold_resources_required = true })


let add_l_value sym value info =
  let@ () = modify_typing_context (fun s -> Context.add_l_value sym value info s) in
  add_sym_eqs [ (sym, value) ]


let get_solver () : solver t = inspect (fun s -> Option.get s.solver)

let init_solver () =
  modify (fun s ->
    let c = s.typing_context in
    let solver = Solver.make c.global in
    LC.Set.iter (Solver.add_assumption solver c.global) c.constraints;
    { s with solver = Some solver })


let get_movable_indices () = inspect (fun s -> s.movable_indices)

let set_movable_indices ixs : unit m = modify (fun s -> { s with movable_indices = ixs })

let add_c_internal lc =
  let@ _ = drop_past_models () in
  let@ s = get_typing_context () in
  let@ solver = get_solver () in
  let@ simp_ctxt = simp_ctxt () in
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  let s = Context.add_c lc s in
  let () = Solver.add_assumption solver s.global lc in
  let@ _ = add_sym_eqs (List.filter_map LC.is_sym_lhs_equality [ lc ]) in
  let@ _ = add_found_equalities lc in
  let@ () = set_typing_context s in
  return ()


let add_r_internal ?(derive_constraints = true) loc (r, Res.O oargs) =
  let@ s = get_typing_context () in
  let@ simp_ctxt = simp_ctxt () in
  let r = Simplify.Request.simp simp_ctxt r in
  let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
  let pointer_facts =
    if derive_constraints then
      Res.pointer_facts ~new_resource:(r, Res.O oargs) ~old_resources:(Context.get_rs s)
    else
      []
  in
  let@ () = set_typing_context (Context.add_r loc (r, O oargs) s) in
  iterM (fun x -> add_c_internal (LC.T x)) pointer_facts


let add_movable_index _loc (pred, ix) =
  let@ ixs = get_movable_indices () in
  let@ () = set_movable_indices ((pred, ix) :: ixs) in
  set_unfold_resources ()


let add_r loc re =
  let@ () = add_r_internal loc re in
  set_unfold_resources ()


let add_rs loc rs =
  let@ () = iterM (add_r_internal loc) rs in
  set_unfold_resources ()


let add_c _loc c =
  let@ () = add_c_internal c in
  set_unfold_resources ()


let add_cs _loc cs =
  let@ () = iterM add_c_internal cs in
  set_unfold_resources ()


(* functions to do with satisfying models *)

let check_models = ref false

let model () =
  let m = Solver.model () in
  let@ ms = get_past_models () in
  let@ c = get_typing_context () in
  let@ () = set_past_models ((m, c) :: ms) in
  return m


let get_just_models () =
  let@ ms = get_past_models () in
  return (List.map fst ms)


let model_has_prop () =
  let is_some_true t = Option.is_some t && IT.is_true (Option.get t) in
  return (fun prop m -> is_some_true (Solver.eval (fst m) prop))


let prove_or_model_with_past_model loc m =
  let@ has_prop = model_has_prop () in
  let@ p_f = provable_internal loc in
  let loc = Locations.other __LOC__ in
  let res lc =
    match lc with
    | LC.T t when has_prop (IT.not_ t loc) m -> `Counterex (lazy m)
    | _ ->
      (match p_f lc with `True -> `True | `False -> `Counterex (lazy (Solver.model ())))
  in
  let res2 lc = match res lc with `Counterex _m -> `False | `True -> `True in
  return (res, res2)


let do_check_model loc m prop =
  Pp.warn loc (Pp.string "doing model consistency check");
  let@ ctxt = get_typing_context () in
  let vs =
    Context.(
      Sym.Map.bindings ctxt.computational @ Sym.Map.bindings ctxt.logical
      |> List.filter (fun (_, (bt_or_v, _)) -> not (has_value bt_or_v))
      |> List.map (fun (nm, (bt_or_v, (loc, _))) -> IT.sym_ (nm, bt_of bt_or_v, loc)))
  in
  let here = Locations.other __LOC__ in
  let eqs =
    List.filter_map
      (fun v ->
        match Solver.eval (fst m) v with
        | None -> None
        | Some x -> Some (IT.eq_ (v, x) here))
      vs
  in
  let@ prover = provable_internal loc in
  match prover (LogicalConstraints.T (IT.and_ (prop :: eqs) here)) with
  | `False -> return ()
  | `True ->
    fail (fun _ -> { loc; msg = Generic (Pp.string "Solver model inconsistent") })


let cond_check_model loc m prop =
  if !check_models then
    do_check_model loc m prop
  else
    return ()


let model_with_internal loc prop =
  let@ ms = get_just_models () in
  let@ has_prop = model_has_prop () in
  match List.find_opt (has_prop prop) ms with
  | Some m -> return (Some m)
  | None ->
    let@ prover = provable_internal loc in
    let here = Locations.other __LOC__ in
    (match prover (LC.T (IT.not_ prop here)) with
     | `True -> return None
     | `False ->
       let@ m = model () in
       let@ () = cond_check_model loc m prop in
       return (Some m))


(* functions for binding return types and associated auxiliary functions *)

let ensure_base_type (loc : Loc.t) ~(expect : BT.t) (has : BT.t) : unit m =
  if BT.equal has expect then
    return ()
  else
    fail (fun _ -> { loc; msg = Mismatch { has = BT.pp has; expect = BT.pp expect } })


let make_return_record loc (record_name : string) record_members =
  let record_s = Sym.fresh_make_uniq record_name in
  (* let record_s = Sym.fresh_make_uniq (TypeErrors.call_prefix call_situation) in *)
  let record_bt = BT.Record record_members in
  let@ () = add_l record_s record_bt (loc, lazy (Sym.pp record_s)) in
  let record_it = IT.sym_ (record_s, record_bt, loc) in
  let member_its =
    List.map
      (fun (s, member_bt) -> IT.recordMember_ ~member_bt (record_it, s) loc)
      record_members
  in
  return (record_it, member_its)


(* This essentially pattern-matches a logical return type against a record pattern.
   `record_it` is the index term for the record, `members` the pattern for its members. *)
let bind_logical_return_internal loc =
  let rec aux members lrt =
    match (members, lrt) with
    | member :: members, LogicalReturnTypes.Define ((s, it), _, lrt) ->
      let@ () = ensure_base_type loc ~expect:(IT.get_bt it) (IT.get_bt member) in
      let@ () = add_c_internal (LC.T (IT.eq__ member it loc)) in
      aux members (LogicalReturnTypes.subst (IT.make_subst [ (s, member) ]) lrt)
    | member :: members, Resource ((s, (re, bt)), _, lrt) ->
      let@ () = ensure_base_type loc ~expect:bt (IT.get_bt member) in
      let@ () = add_r_internal loc (re, Res.O member) in
      aux members (LogicalReturnTypes.subst (IT.make_subst [ (s, member) ]) lrt)
    | members, Constraint (lc, _, lrt) ->
      let@ () = add_c_internal lc in
      aux members lrt
    | [], I -> return ()
    | _ -> assert false
  in
  fun members lrt -> aux members lrt


let bind_logical_return loc members lrt =
  let@ () = bind_logical_return_internal loc members lrt in
  set_unfold_resources ()


(* Same for return types *)
let bind_return loc members (rt : ReturnTypes.t) =
  match (members, rt) with
  | member :: members, Computational ((s, bt), _, lrt) ->
    let@ () = ensure_base_type loc ~expect:bt (IT.get_bt member) in
    let@ () =
      bind_logical_return
        loc
        members
        (LogicalReturnTypes.subst (IT.make_subst [ (s, member) ]) lrt)
    in
    return member
  | _ -> assert false


(* functions for resource inference *)

type changed =
  | Deleted
  | Unchanged
  | Changed of Res.t

let map_and_fold_resources_internal loc (f : Res.t -> 'acc -> changed * 'acc) (acc : 'acc)
  =
  let@ s = get_typing_context () in
  let@ provable_f = provable_internal loc in
  let resources, orig_ix = s.resources in
  let orig_hist = s.resource_history in
  let resources, ix, hist, changed_or_deleted, acc =
    List.fold_right
      (fun (re, i) (resources, ix, hist, changed_or_deleted, acc) ->
        let changed, acc = f re acc in
        match changed with
        | Deleted ->
          let ix, hist = Context.res_written loc i "deleted" (ix, hist) in
          (resources, ix, hist, i :: changed_or_deleted, acc)
        | Unchanged -> ((re, i) :: resources, ix, hist, changed_or_deleted, acc)
        | Changed re ->
          let ix, hist = Context.res_written loc i "changed" (ix, hist) in
          (match re with
           | Q { q; permission; _ }, _ ->
             let here = Locations.other __LOC__ in
             (match provable_f (LC.forall_ q (IT.not_ permission here)) with
              | `True -> (resources, ix, hist, i :: changed_or_deleted, acc)
              | `False ->
                let ix, hist = Context.res_written loc ix "changed" (ix, hist) in
                ((re, ix) :: resources, ix + 1, hist, i :: changed_or_deleted, acc))
           | _ ->
             let ix, hist = Context.res_written loc ix "changed" (ix, hist) in
             ((re, ix) :: resources, ix + 1, hist, i :: changed_or_deleted, acc)))
      resources
      ([], orig_ix, orig_hist, [], acc)
  in
  let@ () =
    set_typing_context { s with resources = (resources, ix); resource_history = hist }
  in
  return (acc, changed_or_deleted)


(* let get_movable_indices () = *)
(*   inspect (fun s -> List.map (fun (pred, nm, _verb) -> (pred, nm)) s.movable_indices) *)

(* the main inference loop *)
let do_unfold_resources loc =
  let rec aux () =
    let@ s = get_typing_context () in
    let@ movable_indices = get_movable_indices () in
    let@ _provable_f = provable_internal (Locations.other __LOC__) in
    let resources, orig_ix = s.resources in
    let _orig_hist = s.resource_history in
    Pp.debug 8 (lazy (Pp.string "-- checking resource unfolds now --"));
    let here = Locations.other __LOC__ in
    let@ true_m = model_with_internal loc (IT.bool_ true here) in
    match true_m with
    | None -> return () (* contradictory state *)
    | Some model ->
      let@ provable_m, provable_f2 = prove_or_model_with_past_model loc model in
      let keep, unpack, extract =
        List.fold_right
          (fun (re, i) (keep, unpack, extract) ->
            match Pack.unpack loc s.global provable_f2 re with
            | Some unpackable ->
              let pname = Req.get_name (fst re) in
              (keep, (i, pname, unpackable) :: unpack, extract)
            | None ->
              let re_reduced, extracted =
                Pack.extractable_multiple provable_m movable_indices re
              in
              let keep' =
                match extracted with
                | [] -> (re_reduced, i) :: keep
                | _ ->
                  (match Pack.resource_empty provable_f2 re_reduced with
                   | `Empty -> keep
                   | `NonEmpty _ -> (re_reduced, i) :: keep)
              in
              (keep', unpack, extracted @ extract))
          resources
          ([], [], [])
      in
      let@ () = set_typing_context { s with resources = (keep, orig_ix) } in
      let do_unpack = function
        | _i, pname, `LRT lrt ->
          let@ _, members =
            make_return_record
              loc
              ("unpack_" ^ Pp.plain (Req.pp_name pname))
              (LogicalReturnTypes.binders lrt)
          in
          bind_logical_return_internal loc members lrt
        | _i, pname, `RES res ->
          let is_owned = match pname with Owned _ -> true | _ -> false in
          iterM (add_r_internal ~derive_constraints:(not is_owned) loc) res
      in
      let@ () = iterM do_unpack unpack in
      let@ () = iterM (add_r_internal loc) extract in
      (match (unpack, extract) with [], [] -> return () | _ -> aux ())
  in
  let@ () = aux () in
  modify (fun s -> { s with unfold_resources_required = false })


let sync_unfold_resources loc =
  let@ needed = inspect (fun s -> s.unfold_resources_required) in
  if not needed then
    return ()
  else
    do_unfold_resources loc


(* functions exposed outside this module that may need to apply resource unfolding using
   sync_unfold_resources *)

let provable loc =
  let@ () = sync_unfold_resources loc in
  provable_internal loc


let all_resources_tagged loc =
  let@ () = sync_unfold_resources loc in
  let@ s = get_typing_context () in
  return s.resources


let all_resources loc =
  let@ () = sync_unfold_resources loc in
  let@ s = get_typing_context () in
  return (Context.get_rs s)


let res_history loc i =
  let@ () = sync_unfold_resources loc in
  let@ s = get_typing_context () in
  return (Context.res_history s i)


let map_and_fold_resources loc f acc =
  let@ () = sync_unfold_resources loc in
  map_and_fold_resources_internal loc f acc


let prev_models_with loc prop =
  let@ () = sync_unfold_resources loc in
  let@ ms = get_just_models () in
  let@ has_prop = model_has_prop () in
  return (List.filter (has_prop prop) ms)


let model_with loc prop =
  let@ () = sync_unfold_resources loc in
  model_with_internal loc prop


(* auxiliary functions for diagnostics *)

let value_eq_group guard x =
  let@ eqs = get_found_equalities () in
  return (EqTable.get_eq_vals eqs guard x)


let test_value_eqs loc guard x ys =
  let here = Locations.other __LOC__ in
  let prop y =
    match guard with
    | None -> LC.T (IT.eq_ (x, y) here)
    | Some t -> LC.T (IT.impl_ (t, IT.eq_ (x, y) here) here)
  in
  let@ prover = provable loc in
  let guard_it = Option.value guard ~default:(IT.bool_ true here) in
  let rec loop group ms = function
    | [] -> return ()
    | y :: ys ->
      let@ has_prop = model_has_prop () in
      let counterex = has_prop (IT.not_ (IT.eq_ (x, y) here) here) in
      if ITSet.mem y group || List.exists counterex ms then
        loop group ms ys
      else (
        match prover (prop y) with
        | `True ->
          let@ () = add_found_equalities (prop y) in
          let@ group = value_eq_group guard x in
          loop group ms ys
        | `False ->
          let@ _ = model () in
          let@ ms = prev_models_with loc guard_it in
          loop group ms ys)
  in
  let@ group = value_eq_group guard x in
  let@ ms = prev_models_with loc guard_it in
  loop group ms ys


module WellTyped = struct
  type nonrec 'a t = 'a t

  include WellTyped.Lift (ErrorReader)
end
