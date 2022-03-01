open Context

type s = {
    typing_context: Context.t;
    solver : Solver.solver;
    sym_eqs : IT.t SymMap.t;
    trace_length : int;         (* for performance debugging *)
  }

type ('a, 'e) t = s -> ('a * s, 'e) Result.t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e


let run (c : Context.t) (m : ('a, 'e) t) : ('a, 'e) Resultat.t = 
  let solver = Solver.make c.global.struct_decls in
  let sym_eqs = SymMap.empty in
  let trace_length = 0 in
  List.iter (Solver.add solver c.global) c.constraints;
  let s = { typing_context = c; solver; sym_eqs; trace_length } in
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


let restore_resources (m : ('a, 'e) t) : ('a, 'e) t =
  fun old_state ->
  match m old_state with
  | Ok (a, new_state) -> 
     let typing_context = 
       {new_state.typing_context with 
         resources = old_state.typing_context.resources} 
     in
     Ok (a, { new_state with typing_context })
  | Error e -> Error e
  






let get_trace_length () = 
  fun s -> Ok (s.trace_length, s)

let increase_trace_length () = 
  fun s -> Ok ((), {s with trace_length = s.trace_length + 1})

let print_with_ctxt printer = 
  let@ s = get () in
  let () = printer s in
  return ()

let get_global () = 
  let@ s = get () in
  return (s.global)

let all_constraints () = 
  let@ s = get () in
  return s.constraints

let simp_constraints () =
  fun s ->
  Ok ((s.sym_eqs, s.typing_context.constraints), s)

let all_resources () = 
  let@ s = get () in
  return s.resources

let make_provable loc =
  fun {typing_context = s; solver; sym_eqs; trace_length} -> 
  let pointer_facts = Resources.RE.pointer_facts s.resources in
  let f ?(shortcut_false=false) lc = 
    Solver.provable ~loc ~shortcut_false ~solver ~global:s.global 
      ~trace_length
      ~assumptions:s.constraints
      ~pointer_facts lc 
  in
  f

let provable loc = 
  fun s -> 
  Ok (make_provable loc s, s)
  

let model () =
  return (Solver.model ())
  


let bound_a sym = 
  let@ s = get () in
  return (Context.bound_a sym s)

let bound_l sym = 
  let@ s = get () in
  return (Context.bound_l sym s)

let get_a sym = 
  let@ s = get () in
  return (Context.get_a sym s)

let get_l sym = 
  let@ s = get () in
  return (Context.get_l sym s)

let add_a sym (bt, sym') = 
  let@ s = get () in
  set (Context.add_a sym (bt, sym') s)

let add_l sym ls =
  let@ s = get () in
  set (Context.add_l sym ls s)

let add_ls lvars = 
  let@ s = get () in
  set (Context.add_ls lvars s)

let add_sym_eqs sym_eqs = 
  fun s -> 
  let sym_eqs = 
    List.fold_left (fun acc (s, v) -> 
        SymMap.add s v acc
      ) s.sym_eqs sym_eqs 
  in
  Ok ((), { s with sym_eqs })
  

let add_c lc = 
  let@ s = get () in
  let@ solver = solver () in
  let@ scs = simp_constraints () in
  let lcs = Simplify.simp_lc_flatten s.global.struct_decls scs lc in
  let s = List.fold_right Context.add_c lcs s in
  let () = List.iter (Solver.add solver s.global) lcs in
  let sym_eqs = List.filter_map (LC.is_sym_lhs_equality) lcs in
  let@ _ = add_sym_eqs sym_eqs in
  set s

let rec add_cs = function
  | [] -> return ()
  | lc :: lcs -> 
     let@ () = add_c lc in 
     add_cs lcs


let add_r oloc r = 
  let@ s = get () in
  let@ scs = simp_constraints () in
  match RE.simp_or_empty s.global.struct_decls scs r with
  | None -> return ()
  | Some r -> set (Context.add_r oloc r s)


let rec add_rs oloc = function
  | [] -> return ()
  | r :: rs -> 
     let@ () = add_r oloc r in
     add_rs oloc rs


type changed = 
  | Deleted
  | Unchanged
  | Unfolded of RE.t list
  | Changed of RE.t

let map_and_fold_resources loc (f : RE.t -> 'acc -> changed * 'acc) (acc : 'acc) = 
  fun s ->
  let provable = make_provable loc s in
  let resources, acc =
    List.fold_right (fun re (resources, acc) ->
        let (changed, acc) = f re acc in
        match changed with
        | Deleted ->
           (resources, acc)
        | Unchanged -> 
           (re :: resources, acc)
        | Unfolded res ->
           (res @ resources, acc)
        | Changed re ->
           match re with
           | QPoint {q; permission; _}
           | QPredicate {q; permission; _} ->
              begin match provable (LC.forall_ (q, Integer) (IT.not_ permission)) with
              | `True -> (resources, acc)
              | `False -> (re :: resources, acc)
              end
           | _ -> 
              (re :: resources, acc)
      ) s.typing_context.resources ([], acc)
  in
  Ok (acc, {s with typing_context = {s.typing_context with resources}})
