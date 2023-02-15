open Context
module IT = IndexTerms
module ITSet = Set.Make(IT)
module SymMap = Map.Make(Sym)
module RET = ResourceTypes


type s = {
    typing_context: Context.t;
    solver : Solver.solver;
    sym_eqs : IT.t SymMap.t;
    equalities: bool Simplify.ITPairMap.t;
    past_models : (Solver.model_with_q * Context.t) list;
    step_trace : Trace.t;
    found_equalities : EqTable.table;
  }

type ('a, 'e) t = s -> ('a * s, 'e) Result.t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e


let run (c : Context.t) (m : ('a, 'e) t) : ('a, 'e) Resultat.t = 
  let solver = Solver.make c.global in
  let sym_eqs = SymMap.empty in
  LCSet.iter (Solver.add_assumption solver c.global) c.constraints;
  let s = { 
      typing_context = c; 
      solver; 
      sym_eqs; 
      equalities = Simplify.ITPairMap.empty;
      past_models = []; 
      step_trace = Trace.empty;
      found_equalities = EqTable.empty;
    } 
  in
  let outcome = m s in
  match outcome with
  | Ok (a, _) -> Ok a
  | Error e -> Error e


let return (a : 'a) : ('a, 'e) t =
  fun s -> Ok (a, s)

let bind (m : ('a, 'e) t) (f : 'a -> ('b, 'e) t) : ('b, 'e) t = 
  fun s -> 
  match m s with
  | Error e -> Error e
  | Ok (x, s') -> (f x) s'



let (let@) = bind

let get () : (Context.t, 'e) t = 
  fun s -> Ok (s.typing_context, s)

let set (c : Context.t) : (unit, 'e) t = 
  fun s -> Ok ((), {s with typing_context = c})

let solver () : (Solver.solver, 'e) t = 
  fun s -> Ok (s.solver, s)

let fail (f : 'e failure) : ('a, 'e) t = 
  fun s -> Error (f s.typing_context)


let pure (m : ('a, 'e) t) : ('a, 'e) t =
  fun s ->
  Solver.push s.solver;
  let outcome = match m s with
    | Ok (a, _) -> Ok (a, s)
    | Error e -> Error e
  in
  Solver.pop s.solver;
  outcome


(* not clear whether Effectful.Make should be used here instead *)
let rec iterM f xs = match xs with
  | [] -> return ()
  | x :: xs ->
    let@ () = f x in
    iterM f xs



let get_models () = fun s -> Ok (s.past_models, s)

let upd_models ms = fun s -> Ok ((), {s with past_models = ms})

let drop_models () = upd_models []

let get_found_eqs () = fun s -> Ok (s.found_equalities, s)

let upd_found_eqs eqs = fun s -> Ok ((), {s with found_equalities = eqs})


let get_step_trace () = fun s -> Ok (s.step_trace, s)

let set_step_trace tr = fun s -> Ok ((), {s with step_trace = tr})

let fail_with_trace m =
  let@ tr = get_step_trace () in
  fail (m tr)

let print_with_ctxt printer = 
  let@ s = get () in
  let () = printer s in
  return ()

let get_global () = 
  let@ s = get () in
  return (s.global)

let set_global global : (unit, 'e) m = 
  let@ ctxt = get () in
  set {ctxt with global}


let all_constraints () = 
  let@ s = get () in
  return s.constraints



let all_resources_tagged () =
  let@ s = get () in
  return s.resources

let all_resources () =
  let@ s = get () in
  return (Context.get_rs s)

let make_simp_ctxt s =
  Simplify.{
      global = s.typing_context.global;
      values = s.sym_eqs;
      equalities = s.equalities;
      lcs = s.typing_context.constraints;
    }


let simp_ctxt () = 
  fun s -> Ok (make_simp_ctxt s, s)


let make_provable loc =
  fun ({typing_context = s; solver; _} as c) -> 
  let simp_ctxt = make_simp_ctxt c in
  let pointer_facts = Resources.pointer_facts (Context.get_rs s) in
  let f lc = 
    Solver.provable 
      ~loc 
      ~solver ~global:s.global 
      ~assumptions:s.constraints
      ~simp_ctxt
      ~pointer_facts 
      lc 
  in
  f

let provable loc = 
  fun s -> 
  Ok (make_provable loc s, s)
  


  


let model () =
  let m = Solver.model () in
  let@ ms = get_models () in
  let@ c = get () in
  let@ () = upd_models ((m, c) :: ms) in
  return m

let get_just_models () =
  let@ ms = get_models () in
  return (List.map fst ms)

let model_has_prop prop =
  let@ global = get_global () in
  let is_some_true t = Option.is_some t && IT.is_true (Option.get t) in
  return (fun m -> is_some_true (Solver.eval global (fst m) prop))

let prev_models_with loc prop =
  let@ ms = get_just_models () in
  let@ has_prop = model_has_prop prop in
  return (List.filter has_prop ms)

let model_with loc prop =
  let@ ms = get_just_models () in
  let@ has_prop = model_has_prop prop in
  match List.find_opt has_prop ms with
    | Some m -> return (Some m)
    | None -> begin
      let@ prover = provable loc in
      match prover (LC.t_ (IT.not_ prop)) with
        | `True -> return None
        | `False ->
            let@ m = model () in
            return (Some m)
  end

let bound_a sym = 
  let@ s = get () in
  return (Context.bound_a sym s)

let bound_l sym = 
  let@ s = get () in
  return (Context.bound_l sym s)

let bound sym = 
  let@ s = get () in
  return (Context.bound sym s)

let get_a sym = 
  let@ s = get () in
  return (Context.get_a sym s)

let get_l sym = 
  let@ s = get () in
  return (Context.get_l sym s)

let add_a sym bt info = 
  let@ s = get () in
  set (Context.add_a sym bt info s)

let add_l sym bt info =
  let@ s = get () in
  set (Context.add_l sym bt info s)


let remove_a sym = 
  let@ s = get () in
  set (Context.remove_a sym s)

let remove_as = iterM remove_a


let rec add_ls = function
  | [] -> return ()
  | (s, ls, info) :: lvars ->
     let@ () = add_l s ls info in
     add_ls lvars

let add_sym_eqs sym_eqs = 
  fun s -> 
  let sym_eqs = 
    List.fold_left (fun acc (s, v) -> 
        SymMap.add s v acc
      ) s.sym_eqs sym_eqs 
  in
  Ok ((), { s with sym_eqs })

let add_equalities new_equalities =
  fun s ->
  let equalities = 
    List.fold_left (fun acc ((a, b), eq_or_not) ->
        Simplify.ITPairMap.add (a,b) eq_or_not acc
      )
      s.equalities new_equalities 
  in
  Ok ((), { s with equalities })

let add_found_equalities lc =
  let@ eqs = get_found_eqs () in
  upd_found_eqs (EqTable.add_lc_eqs eqs lc)


let add_c lc = 
  let@ _ = drop_models () in
  let@ s = get () in
  let@ solver = solver () in
  let@ simp_ctxt = simp_ctxt () in
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  let s = Context.add_c lc s in
  let () = Solver.add_assumption solver s.global lc in
  let@ _ = add_sym_eqs (List.filter_map (LC.is_sym_lhs_equality) [lc]) in
  let@ _ = add_equalities (List.filter_map LC.is_equality [lc]) in
  let@ _ = add_found_equalities lc in
  set s

let add_cs = iterM add_c




let add_r (r, RE.O oargs) = 
  let@ s = get () in
  let@ simp_ctxt = simp_ctxt () in
  match Simplify.ResourceTypes.simp_or_empty simp_ctxt r with
  | None -> return ()
  | Some r ->
    let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
    set (Context.add_r (r, O oargs) s)

let add_rs = iterM add_r


type changed = 
  | Deleted
  | Unchanged
  | Unfolded of RE.t list
  | Changed of RE.t

let map_and_fold_resources_adj loc (f : RE.t -> 'acc -> changed * 'acc) (acc : 'acc) =
  fun s ->
  let provable = make_provable loc s in
  let (resources, orig_ix) = s.typing_context.resources in
  let resources, ix, acc =
    List.fold_right (fun (re, i) (resources, ix, acc) ->
        let (changed, acc) = f re acc in
        match changed with
        | Deleted ->
           (resources, ix, acc)
        | Unchanged -> 
           ((re, i) :: resources, ix, acc)
        | Unfolded res ->
           let tagged = List.mapi (fun j re -> (re, ix + j)) res in
           (tagged @ resources, ix + List.length res, acc)
        | Changed re ->
           match re with
           | (Q {q; permission; _}, _) ->
              begin match provable (LC.forall_ (q, Integer) (IT.not_ permission)) with
              | `True -> (resources, ix, acc)
              | `False -> ((re, ix) :: resources, ix + 1, acc)
              end
           | _ -> 
              ((re, ix) :: resources, ix + 1, acc)
      ) resources ([], orig_ix, acc)
  in
  Ok ((acc, orig_ix),
    {s with typing_context = {s.typing_context with resources = (resources, ix)}})



let map_and_fold_resources loc f acc =
  let@ (acc, orig_ix) = map_and_fold_resources_adj loc f acc in
  return acc

let get_loc_trace () =
  let@ c = get () in
  return c.location_trace

let set_loc_trace tr = 
  let@ c = get () in
  set ({c with location_trace = tr})

let add_loc_trace loc = 
  let@ locs = get_loc_trace () in
  set_loc_trace (loc :: locs)

let in_loc_trace tr f =
  let@ prev_tr = get_loc_trace () in
  let@ _ = set_loc_trace tr in
  let@ x = f () in
  let@ _ = set_loc_trace prev_tr in
  return x

let finish_trace_step do_add ctxt1 () =
  let@ ctxt2 = get () in
  let@ tr = get_step_trace () in
  let@ () = set_step_trace (do_add (ctxt1, ctxt2) tr) in
  return ()

let begin_trace_of_step pat expr =
  let@ ctxt1 = get () in
  return (finish_trace_step (Trace.add_trace_step pat expr) ctxt1)

let begin_trace_of_pure_step pat pexpr =
  let@ ctxt1 = get () in
  return (finish_trace_step (Trace.add_pure_trace_step pat pexpr) ctxt1)

let get_resource_predicate_def loc id =
  let@ global = get_global () in
  let open TypeErrors in
  match Global.get_resource_predicate_def global id with
    | Some def -> return def
    | None -> fail (fun _ -> {loc; msg = Unknown_resource_predicate {id;
        logical = Option.is_some (Global.get_logical_predicate_def global id)}})


let todo_opt_get_resource_predicate_def_s id =
  let@ global = get_global () in
  let odef = 
    SymMap.choose_opt
      (SymMap.filter (fun s _ -> String.equal (Tools.todo_string_of_sym s) id)
         global.resource_predicates)
  in
  return odef

let todo_opt_get_logical_predicate_def_s id =
  let@ global = get_global () in
  let odef = 
    SymMap.choose_opt
      (SymMap.filter (fun s _ -> String.equal (Tools.todo_string_of_sym s) id)
         global.logical_predicates)
  in
  return odef

let todo_get_resource_predicate_def_s loc id =
  let open TypeErrors in
  let@ odef = todo_opt_get_resource_predicate_def_s id in
  match odef with
  | Some def -> return def
  | None -> 
     let@ odef = todo_opt_get_logical_predicate_def_s id in
     fail (fun _ -> {loc; msg = Unknown_resource_predicate {id = Sym.fresh_named id;
                                  logical = Option.is_some odef}})

let todo_get_logical_predicate_def_s loc id =
  let open TypeErrors in
  let@ odef = todo_opt_get_logical_predicate_def_s id in
  match odef with
  | Some def -> return def
  | None -> 
     let@ odef = todo_opt_get_resource_predicate_def_s id in
     fail (fun _ -> {loc; msg = Unknown_logical_predicate {id = Sym.fresh_named id;
                                  resource = Option.is_some odef}})


let get_resource_predicate_def_s loc id =
  let open TypeErrors in
  let@ global = get_global () in
  match Global.get_resource_predicate_def global id with
  | Some def -> return def
  | None -> fail (fun _ -> {loc; msg = Unknown_resource_predicate {id;
      logical = Option.is_some (Global.get_logical_predicate_def global id)}})


let get_logical_predicate_def loc id =
  let@ global = get_global () in
  let open TypeErrors in
  match Global.get_logical_predicate_def global id with
  | Some def -> return def
  | None -> fail (fun _ -> {loc; msg = Unknown_logical_predicate {id;
      resource = Option.is_some (Global.get_resource_predicate_def global id)}})

let get_struct_decl loc tag = 
  let open TypeErrors in
  let@ global = get_global () in
  match SymMap.find_opt tag global.struct_decls with
  | Some decl -> return decl
  | None -> fail (fun _ -> {loc; msg = Unknown_struct tag})

let get_datatype loc tag = 
  let open TypeErrors in
  let@ global = get_global () in
  match SymMap.find_opt tag global.datatypes with
  | Some dt -> return dt
  | None -> fail (fun _ -> {loc; msg = Unknown_datatype tag})

let get_datatype_constr loc tag = 
  let open TypeErrors in
  let@ global = get_global () in
  match SymMap.find_opt tag global.datatype_constrs with
  | Some info -> return info
  | None -> fail (fun _ -> {loc; msg = Unknown_datatype_constr tag})



let get_member_type loc tag member layout : (Sctypes.t, TypeErrors.t) m = 
  let open TypeErrors in
  match List.assoc_opt Id.equal member (Memory.member_types layout) with
  | Some membertyp -> return membertyp
  | None -> fail (fun _ -> {loc; msg = Unknown_member (tag, member)})

let get_struct_member_type loc tag member =
  let@ decl = get_struct_decl loc tag in
  let@ ty = get_member_type loc tag member decl in
  return ty

let get_fun_decl loc fsym = 
  let open TypeErrors in
  let@ global = get_global () in
  match Global.get_fun_decl global fsym with
  | Some t -> return t
  | None -> fail (fun _ -> {loc = Loc.unknown; msg = Unknown_function fsym})



let add_struct_decl tag layout : (unit, 'e) m = 
  let@ global = get_global () in
  set_global { global with struct_decls = SymMap.add tag layout global.struct_decls }

let add_fun_decl fname entry = 
  let@ global = get_global () in
  set_global { global with fun_decls = SymMap.add fname entry global.fun_decls }



let add_resource_predicate name entry = 
  let@ global = get_global () in
  set_global { global with resource_predicates = Global.SymMap.add name entry global.resource_predicates }


let add_logical_predicate name entry = 
  let@ global = get_global () in
  set_global { global with logical_predicates = Global.SymMap.add name entry global.logical_predicates }

let add_datatype name entry = 
  let@ global = get_global () in
  set_global { global with datatypes = SymMap.add name entry global.datatypes }

let add_datatype_constr name entry = 
  let@ global = get_global () in
  set_global { global with datatype_constrs = SymMap.add name entry global.datatype_constrs }





let value_eq_group guard x =
  let@ eqs = get_found_eqs () in
  return (EqTable.get_eq_vals eqs guard x)

let test_value_eqs loc guard x ys =
  let prop y = match guard with
    | None -> LC.t_ (IT.eq_ (x, y))
    | Some t -> LC.t_ (IT.impl_ (t, IT.eq_ (x, y)))
  in
  let@ prover = provable loc in
  let guard_it = Option.value guard ~default:(IT.bool_ true) in
  let rec loop group ms = function
    | [] -> return ()
    | y :: ys ->
      let@ counterex = model_has_prop (IT.not_ (IT.eq_ (x, y))) in
      if ITSet.mem y group || List.exists counterex ms
      then loop group ms ys
      else match prover (prop y) with
        | `True ->
            let@ () = add_found_equalities (prop y) in
            let@ group = value_eq_group guard x in
            loop group ms ys
        | `False ->
            let@ _ = model () in
            let@ ms = prev_models_with loc guard_it in
            loop group ms ys
  in
  let@ group = value_eq_group guard x in
  let@ ms = prev_models_with loc guard_it in
  loop group ms ys


let set_statement_locs statement_locs = 
  let@ ctxt = get () in
  set { ctxt with statement_locs }



let embed_resultat (m : ('a, 'e) Resultat.t) : ('a, 'e) m = 
  fun s ->
  match m with
  | Ok r -> Ok (r , s)
  | Error e -> Error e
