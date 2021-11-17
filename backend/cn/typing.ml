open Context

type s = {
    typing_context: Context.t;
    solver : Solver.solver;
  }

type ('a, 'e) t = s -> ('a * s, 'e) Result.t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = Context.t -> 'e


let run (c : Context.t) (m : ('a, 'e) t) : ('a, 'e) Resultat.t = 
  let solver = Solver.make () in
  List.iter (Solver.add solver c.global) c.constraints;
  let s = { typing_context = c; solver } in
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

let all_resources () = 
  let@ s = get () in
  return s.resources

let provable =
  let@ s = get () in
  let@ solver = solver () in
  let f ?(shortcut_false=false) lc = 
    Solver.provable ~shortcut_false solver s.global s.constraints lc 
  in
  return f

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

let add_c lc = 
  let@ s = get () in
  let@ solver = solver () in
  let lcs = Simplify.simp_lc_flatten s.global.struct_decls s.constraints lc in
  let s = List.fold_right Context.add_c lcs s in
  let () = List.iter (Solver.add solver s.global) lcs in
  set s

let rec add_cs = function
  | [] -> return ()
  | lc :: lcs -> 
     let@ () = add_c lc in 
     add_cs lcs


let add_r oloc r = 
  let@ s = get () in
  let r = RE.simp s.global.struct_decls s.constraints r in
  let (s, lcs) = Context.add_r oloc r s in
  let@ () = set s in
  return lcs

let map_and_fold_resources f acc =
  let@ s = get () in
  let (s, acc) = Context.map_and_fold_resources f s acc in
  let@ () = set s in
  return acc


