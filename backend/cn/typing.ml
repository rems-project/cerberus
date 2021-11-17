open Context

type s = Context.t

type ('a, 'e) t = s -> ('a * s, 'e) Result.t
type ('a, 'e) m = ('a, 'e) t
type 'e failure = s -> 'e


let run s m = 
  let () = Solver.push () in
  let outcome = m s in
  let () = Solver.pop () in
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

let get () : ('a, 'e) t = 
  fun s -> Ok (s, s)

let set (s : 's) : (unit, 'e) t = 
  fun _ -> Ok ((), s)


let fail (f : s -> 'e) : ('a, 'e) t = 
  fun s -> Error (f s)


let pure (m : ('a, 'e) t) : ('a, 'e) t =
  fun s ->
  Solver.push ();
  let outcome = match m s with
    | Ok (a, _) -> Ok (a, s)
    | Error e -> Error e
  in
  Solver.pop ();
  outcome


let restore_resources (m : ('a, 'e) t) : ('a, 'e) t =
  fun old_state ->
  match m old_state with
  | Ok (a, new_state) -> 
     Ok (a, { new_state with resources = old_state.resources })
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
  let f ?(shortcut_false=false) lc = 
    Solver.provable ~shortcut_false s.global s.constraints lc 
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
  set (Context.add_c lc s)

let add_cs lcs = 
  let@ s = get () in
  set (Context.add_cs lcs s)

let add_r oloc r = 
  let@ s = get () in
  set (Context.add_r oloc r s)

let map_and_fold_resources f acc =
  let@ s = get () in
  let (s, acc) = Context.map_and_fold_resources f s acc in
  let@ () = set s in
  return acc


let all_vars () = 
  let@ s = get () in
  return (Context.all_vars s)

let bind_return_type oloc sym rt = 
  let@ s = get () in
  set (Context.bind oloc s sym rt)

let bind_logical_return_type oloc lrt = 
  let@ s = get () in
  set (Context.bind_logical oloc s lrt)

let logically_bind_return_type oloc rt = 
  let@ s = get () in
  let ((bt, sym), s) = Context.bind_logically oloc s rt in
  let@ () = set s in
  return (bt, sym)
