open Context

type e = TypeErrors.type_error
type s = Context.t

type error = (Locations.loc * e) * string option 

type 'a t = { c : s -> ('a * s, error) Result.t }
type 'a m = 'a t
type failure = Context.t -> TypeErrors.type_error


let run m s = 
  m.c s


let return (a : 'a) : 'a t =
  { c = fun s -> Ok (a, s) }

let bind (m : 'a t) (f : 'a -> 'b t) : 'b t = 
  let c s = match m.c s with
    | Error e -> Error e
    | Ok (x, s') -> (f x).c s'
  in
  { c }

let (let@) = bind

let get () : 'a t = 
  { c = fun s -> Ok (s, s) }

let set (s : 's) : unit t = 
  { c = fun _ -> Ok ((), s) }


let error loc e = 
  ((loc, e), Tools.do_stack_trace ())

let fail (loc: Loc.loc) (e: e) : 'a t = 
  { c = fun _ -> Error (error loc e) }

let failS (loc : Loc.loc) (f : failure) : 'a t = 
  { c = fun s -> Error (error loc (f s)) }


let pure (m : 'a t) : 'a t =
  let c s = 
    Z3.Solver.push s.solver;
    let outcome = match m.c s with
      | Ok (a, _) -> Ok (a, s)
      | Error e -> Error e
    in
    Z3.Solver.pop s.solver 1;
    outcome
  in
  { c }




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
  return (fun lc -> Solver.provable s.global.struct_decls s.solver lc)

let model () =
  let@ s = get () in
  return (Solver.model s.solver)

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
