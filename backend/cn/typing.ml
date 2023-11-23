open Context
module IT = IndexTerms
module ITSet = Set.Make(IT)
module SymMap = Map.Make(Sym)
module RET = ResourceTypes
module RE = Resources
open TypeErrors


type s = {
    typing_context: Context.t;
    solver : Solver.solver;
    sym_eqs : IT.t SymMap.t;
    equalities: bool Simplify.ITPairMap.t;
    past_models : (Solver.model_with_q * Context.t) list;
    step_trace : Trace.t;
    found_equalities : EqTable.table;
    movable_indices: (RET.predicate_name * IT.t) list;
  }

type 'a t = s -> ('a * s, TypeErrors.t) Result.t
type 'a m = 'a t
type failure = Context.t -> TypeErrors.t


let run (c : Context.t) (m : ('a) t) : ('a) Resultat.t = 
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
      movable_indices = [];
    } 
  in
  let outcome = m s in
  match outcome with
  | Ok (a, _) -> Ok a
  | Error e -> Error e


let return (a : 'a) : ('a) t =
  fun s -> Ok (a, s)

let bind (m : ('a) t) (f : 'a -> ('b) t) : ('b) t = 
  fun s -> 
  match m s with
  | Error e -> Error e
  | Ok (x, s') -> (f x) s'



let (let@) = bind

let get () : (Context.t) t = 
  fun s -> Ok (s.typing_context, s)

let set (c : Context.t) : (unit) t = 
  fun s -> Ok ((), {s with typing_context = c})

let solver () : (Solver.solver) t = 
  fun s -> Ok (s.solver, s)

let fail (f : failure) : ('a) t = 
  fun s -> Error (f s.typing_context)


let pure (m : ('a) t) : ('a) t =
  fun s ->
  Solver.push s.solver;
  let outcome = match m s with
    | Ok (a, _) -> Ok (a, s)
    | Error e -> Error e
  in
  Solver.pop s.solver;
  outcome


module Eff = Effectful.Make(struct
  type 'a m = 'a t
  let bind = bind
  let return = return
  end)

let iterM = Eff.ListM.iterM


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

let set_global global : (unit) m = 
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
      simp_hook = (fun _ -> None);
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

let add_a_value sym value info = 
  let@ s = get () in
  set (Context.add_a_value sym value info s)

let add_l sym bt info =
  let@ s = get () in
  set (Context.add_l sym bt info s)

let add_l_value sym value info = 
  let@ s = get () in
  set (Context.add_l_value sym value info s)

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


let add_c_internal lc = 
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
  let@ () = set s in
  return ()
  
let add_r_internal loc (r, RE.O oargs) =
  let@ s = get () in
  let@ simp_ctxt = simp_ctxt () in
  let r = Simplify.ResourceTypes.simp simp_ctxt r in
  let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
  set (Context.add_r loc (r, O oargs) s)  
  
  
type changed = 
  | Deleted
  | Unchanged
  | Changed of RE.t

  

  
let map_and_fold_resources loc
    (f : RE.t -> 'acc -> changed * 'acc)
    (acc : 'acc) =
  let@ s = get () in
  let@ provable_f = provable loc in
  let (resources, orig_ix) = s.resources in
  let orig_hist = s.resource_history in
  let resources, ix, hist, changed_or_deleted, acc =
    List.fold_right (fun (re, i) (resources, ix, hist, changed_or_deleted, acc) ->
        let (changed, acc) = f re acc in
        match changed with
        | Deleted ->
           let (ix, hist) = Context.res_written loc i "deleted" (ix, hist) in
           (resources, ix, hist, i::changed_or_deleted, acc)
        | Unchanged ->
           ((re, i) :: resources, ix, hist, changed_or_deleted, acc)
        | Changed re ->
           let (ix, hist) = Context.res_written loc i "changed" (ix, hist) in
           begin match re with
           | (Q {q; permission; _}, _) ->
              begin match provable_f (LC.forall_ (q, Integer) (IT.not_ permission)) with
              | `True -> (resources, ix, hist, i::changed_or_deleted, acc)
              | `False ->
                 let (ix, hist) = Context.res_written loc ix "changed" (ix, hist) in
                 ((re, ix) :: resources, ix + 1, hist, i::changed_or_deleted, acc)
              end
           | _ -> 
              let (ix, hist) = Context.res_written loc ix "changed" (ix, hist) in
              ((re, ix) :: resources, ix + 1, hist, i::changed_or_deleted, acc)
           end
      ) resources ([], orig_ix, orig_hist, [], acc)
  in
  let@ () = set {s with resources = (resources, ix); resource_history = hist} in
  return (acc, changed_or_deleted)  
  


  
let ensure_logical_sort (loc : Loc.loc) ~(expect : LS.t) (has : LS.t) : (unit) m =
  if LS.equal has expect 
  then return () 
  else fail (fun _ -> {loc; msg = Mismatch {has = BT.pp has; expect = BT.pp expect}})

let ensure_base_type (loc : Loc.loc) ~(expect : BT.t) (has : BT.t) : (unit) m =
  ensure_logical_sort loc ~expect has  


let make_return_record loc (record_name:string) record_members = 
  let record_s = Sym.fresh_make_uniq record_name in
  (* let record_s = Sym.fresh_make_uniq (TypeErrors.call_prefix call_situation) in *)
  let record_bt = BT.Record record_members in
  let@ () = add_l record_s record_bt (loc, lazy (Sym.pp record_s)) in
  let record_it = IT.sym_ (record_s, record_bt) in
  let member_its = 
    List.map (fun (s, member_bt) -> 
        IT.recordMember_ ~member_bt (record_it, s)
      ) record_members 
  in
  return (record_it, member_its)



  


(* This essentially pattern-matches a logical return type against a
   record pattern. `record_it` is the index term for the record,
   `members` the pattern for its members. *)
let bind_logical_return_internal loc = 
  let rec aux members lrt = 
    match members, lrt with
    | member :: members, 
      LogicalReturnTypes.Define ((s, it), _, lrt) ->
       let@ () = ensure_base_type loc ~expect:(IT.bt it) (IT.bt member) in
       let@ () = add_c_internal (LC.t_ (IT.eq__ member it)) in
       aux members (LogicalReturnTypes.subst (IT.make_subst [(s, member)]) lrt)
    | member :: members,
      Resource ((s, (re, bt)), _, lrt) -> 
       let@ () = ensure_base_type loc ~expect:bt (IT.bt member) in
       let@ () = add_r_internal loc (re, RE.O member) in
       aux members (LogicalReturnTypes.subst (IT.make_subst [(s, member)]) lrt)
    | members,
      Constraint (lc, _, lrt) -> 
       let@ () = add_c_internal lc in
       aux members lrt
    | [],
      I -> 
       return ()
    | _ ->
       assert false
  in
  fun members lrt -> aux members lrt

let get_movable_indices () = 
  fun s ->
  Ok (s.movable_indices, s)  
  

(* copying and adjusting map_and_fold_resources *)
let unfold_resources loc = 
  let rec aux () =
    let@ s = get () in
    let@ movable_indices = get_movable_indices () in
    let@ provable_f = provable Locations.unknown in
    let (resources, orig_ix) = s.resources in
    let _orig_hist = s.resource_history in
    match provable_f (LC.t_ (IT.bool_ false)) with
    | `True -> return ()
    | `False ->
    let keep, unpack, extract =
      List.fold_right (fun (re, i) (keep, unpack, extract) ->
          match Pack.unpack loc s.global provable_f re with
          | Some unpackable -> 
              let pname = RET.pp_predicate_name (RET.predicate_name (fst re)) in
              (keep, (i, pname, unpackable) :: unpack, extract)
          | None -> 
              let re_reduced, extracted =
                Pack.extractable_multiple loc provable_f movable_indices re in
              let keep' = match extracted with
               | [] -> (re_reduced, i) :: keep
               | _ ->
                  match Pack.resource_empty provable_f re_reduced with
                  | `Empty -> keep
                  | `NonEmpty _ -> (re_reduced, i) :: keep
              in
              (keep', unpack, extracted @ extract)
        ) resources ([], [], [])
    in
    let@ () = set {s with resources = (keep, orig_ix)} in
    let do_unpack = function
      | (_i, pname, `LRT lrt) ->
          let@ _, members = make_return_record loc ("unpack_" ^ Pp.plain pname) (LogicalReturnTypes.binders lrt) in
          bind_logical_return_internal loc members lrt
      | (_i, _pname, `RES res) ->
          iterM (add_r_internal loc) res
    in
    let@ () = iterM do_unpack unpack in
    let@ () = iterM (add_r_internal loc) extract in
    match unpack, extract with
    | [], [] -> return ()
    | _ -> 
      aux () 
  in
  aux ()









let res_history i =
  let@ s = get () in
  return (Context.res_history s i)




let get_loc_trace () =
  let@ c = get () in
  return c.location_trace

let set_loc_trace tr = 
  let@ c = get () in
  set ({c with location_trace = tr})

let add_loc_trace loc = 
  let@ locs = get_loc_trace () in
  set_loc_trace (loc :: locs)

(* let in_loc_trace tr f = *)
(*   let@ prev_tr = get_loc_trace () in *)
(*   let@ _ = set_loc_trace tr in *)
(*   let@ x = f () in *)
(*   let@ _ = set_loc_trace prev_tr in *)
(*   return x *)

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
  match Global.get_resource_predicate_def global id with
    | Some def -> return def
    | None -> fail (fun _ -> {loc; msg = Unknown_resource_predicate {id;
        logical = Option.is_some (Global.get_logical_function_def global id)}})






let get_logical_function_def loc id =
  let@ global = get_global () in
  match Global.get_logical_function_def global id with
  | Some def -> return def
  | None -> fail (fun _ -> {loc; msg = Unknown_logical_function {id;
      resource = Option.is_some (Global.get_resource_predicate_def global id)}})

let get_struct_decl loc tag = 
  let@ global = get_global () in
  match SymMap.find_opt tag global.struct_decls with
  | Some decl -> return decl
  | None -> fail (fun _ -> {loc; msg = Unknown_struct tag})

let get_datatype loc tag = 
  let@ global = get_global () in
  match SymMap.find_opt tag global.datatypes with
  | Some dt -> return dt
  | None -> fail (fun _ -> {loc; msg = Unknown_datatype tag})

let get_datatype_constr loc tag = 
  let@ global = get_global () in
  match SymMap.find_opt tag global.datatype_constrs with
  | Some info -> return info
  | None -> fail (fun _ -> {loc; msg = Unknown_datatype_constr tag})



let get_member_type loc tag member layout : (Sctypes.t) m = 
  let member_types = Memory.member_types layout in
  match List.assoc_opt Id.equal member member_types with
  | Some membertyp -> return membertyp
  | None -> fail (fun _ -> {loc; msg = Unexpected_member (List.map fst member_types, member)})

let get_struct_member_type loc tag member =
  let@ decl = get_struct_decl loc tag in
  let@ ty = get_member_type loc tag member decl in
  return ty

let get_fun_decl loc fsym = 
  let@ global = get_global () in
  match Global.get_fun_decl global fsym with
  | Some t -> return t
  | None -> fail (fun _ -> {loc; msg = Unknown_function fsym})

let get_lemma loc lsym = 
  let@ global = get_global () in
  match Global.get_lemma global lsym with
  | Some t -> return t
  | None -> fail (fun _ -> {loc; msg = Unknown_lemma lsym})



let add_struct_decl tag layout : (unit) m = 
  let@ global = get_global () in
  set_global { global with struct_decls = SymMap.add tag layout global.struct_decls }

let add_fun_decl fname entry = 
  let@ global = get_global () in
  set_global { global with fun_decls = SymMap.add fname entry global.fun_decls }

let add_lemma lemma_s (loc, lemma_typ) =
  let@ global = get_global () in
  set_global { global with lemmata = SymMap.add lemma_s (loc, lemma_typ) global.lemmata }


let add_resource_predicate name entry = 
  let@ global = get_global () in
  set_global { global with resource_predicates = Global.SymMap.add name entry global.resource_predicates }


let add_logical_function name entry = 
  let@ global = get_global () in
  set_global { global with logical_functions = Global.SymMap.add name entry global.logical_functions }

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


let get_solver_focused_terms () =
  let@ global = get_global () in
  let@ assumptions = all_constraints () in
  let@ s = solver () in
  let@ ctxt = get () in
  let@ rs = all_resources () in
  let pointer_facts = Resources.pointer_facts rs in
  let assumptions = ctxt.constraints in
  let terms = Solver.get_solver_focused_terms s ~assumptions ~pointer_facts global in
  return terms


let embed_resultat (m : ('a) Resultat.t) : ('a) m = 
  fun s ->
  match m with
  | Ok r -> Ok (r , s)
  | Error e -> Error e


let add_movable_index_internal e : unit m =
  fun s ->
  Ok ((), {s with movable_indices = e :: s.movable_indices})


let add_movable_index loc e = 
  let@ () = add_movable_index_internal e in
  unfold_resources loc

let add_r loc re = 
   let@ () = add_r_internal loc re in
   unfold_resources loc

let add_rs loc rs =
  let@ () = iterM (add_r_internal loc) rs in
  unfold_resources loc

let add_c loc c =
  let@ () = add_c_internal c in
  unfold_resources loc

let add_alloc loc ~ptr ~size =
  let@ ctxt = get () in
  add_c loc @@ Context.add_alloc ~ptr ~size ctxt

let add_cs loc cs = 
  let@ () = iterM add_c_internal cs in
  unfold_resources loc
  

let bind_logical_return loc members lrt = 
  let@ () = bind_logical_return_internal loc members lrt in
  unfold_resources loc

(* Same for return types *)
let bind_return loc members (rt : ReturnTypes.t) =
  match members, rt with
  | member :: members,
    Computational ((s, bt), _, lrt) ->
     let@ () = ensure_base_type loc ~expect:bt (IT.bt member) in
     let@ () = bind_logical_return loc members 
                 (LogicalReturnTypes.subst (IT.make_subst [(s, member)]) lrt) in
     return member
  | _ ->
     assert false


  

