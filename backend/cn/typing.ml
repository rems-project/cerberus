module Loc = Locations

module Make(L : Local.S) : sig

  type error = 
    Locations.loc * Tools.stacktrace option * TypeErrors.type_error Lazy.t


  type 'a t
  type 'a m = 'a t
  val run : 'a m -> L.t -> ('a * L.t, error) Result.t
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val (let@) : 'a m -> ('a -> 'b m) -> 'b m
  val fail : Locations.t -> TypeErrors.type_error Lazy.t -> 'a m
  val attempt : (('a m) Lazy.t) List1.t -> 'a m
  val get: unit -> L.t m
  val pure : 'a m -> 'a m
  val all_computational : unit -> ((Sym.t * (BaseTypes.t * Sym.t)) list) m
  val all_logical : unit -> ((Sym.t * LogicalSorts.t) list) m
  val all_constraints : unit -> (LogicalConstraints.t list) m
  val all_resources : unit -> (Resources.RE.t list) m
  val solver : unit -> Z3.Solver.solver m
  val bound : Sym.t -> Kind.t -> bool m
  val get_a : Sym.t -> (BaseTypes.t * Sym.t) m
  val get_l : Sym.t -> LogicalSorts.t m
  val add_a : Sym.t -> (BaseTypes.t * Sym.t) -> unit m
  val add_l : Sym.t -> LogicalSorts.t -> unit m
  val add_c : LogicalConstraints.t -> unit m
  val add_cs : LogicalConstraints.t list -> unit m
  val add_r : Local.where option -> Resources.RE.t -> unit m
  val remove_resource : Resources.RE.t -> unit m
  val map_and_fold_resources : 
    (Resources.RE.t -> 'acc -> Resources.RE.t * 'acc) -> 
    'acc -> 'acc m
  val all_vars : unit -> (Sym.t list) m
  val bind_return_type : Local.where option -> Sym.t -> ReturnTypes.t -> unit m
  val bind_logical_return_type : Local.where option -> LogicalReturnTypes.t -> unit m
  val logically_bind_return_type : Local.where option -> ReturnTypes.t -> (BaseTypes.t * Sym.t) m

end = struct

  type e = TypeErrors.type_error
  type s = L.t

  type error = 
    Locations.loc * Tools.stacktrace option * e Lazy.t

  type 'a t = 
    { c : s -> ('a * s, error) Result.t }

  type 'a m = 
    'a t

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
    (loc, Tools.do_stack_trace (),  e)

  let fail (loc: Locations.loc) (e: 'e Lazy.t) : 'a t = 
    { c = fun _ -> Error (error loc e) }


  let rec attempt (fs : (('a t) Lazy.t) List1.t) : 'a t = 
    let c s = 
      let (hd, tl) = List1.dest fs in
      let hd_run = Lazy.force hd in
      match hd_run.c s, tl with
      | Ok (a, s'), _ -> 
         Ok (a, s')
      | Error _, hd' :: tl' -> 
         (attempt (List1.make (hd', tl'))).c s
      | Error err, _ -> 
         Error err
    in
    { c }



  let pure (m : 'a t) : 'a t =
    let c s = 
      Z3.Solver.push (L.solver s);
      let outcome = match m.c s with
        | Ok (a, _) -> Ok (a, s)
        | Error e -> Error e
      in
      Z3.Solver.pop (L.solver s) 1;
      outcome
    in
    { c }




  let all_computational () = 
    let@ l = get () in
    return (L.all_computational l)

  let all_logical () = 
    let@ l = get () in
    return (L.all_logical l)

  let all_constraints () = 
    let@ l = get () in
    return (L.all_constraints l)

  let all_resources () = 
    let@ l = get () in
    return (L.all_resources l)

  let solver () =
    let@ l = get () in
    return (L.solver l)

  let bound s kind = 
    let@ l = get () in
    return (L.bound s kind l)

  let get_a s = 
    let@ l = get () in
    return (L.get_a s l)

  let get_l s = 
    let@ l = get () in
    return (L.get_l s l)

  let add_a s (bt, s') = 
    let@ l = get () in
    set (L.add_a s (bt, s') l)

  let add_l s ls =
    let@ l = get () in
    set (L.add_l s ls l)

  let add_c lc = 
    let@ l = get () in
    set (L.add_c lc l)

  let add_cs lcs = 
    let@ l = get () in
    set (L.add_cs lcs l)

  let add_r oloc r = 
    let@ l = get () in
    set (L.add_r oloc r l)

  let remove_resource re = 
    let@ l = get () in
    set (L.remove_resource re l)

  let map_and_fold_resources f acc =
    let@ l = get () in
    let (l', acc) = L.map_and_fold_resources f l acc in
    let@ () = set l' in
    return acc


  let all_vars () = 
    let@ l = get () in
    return (L.all_vars l)

  let bind_return_type oloc s rt = 
    let@ l = get () in
    set (L.bind oloc l s rt)

  let bind_logical_return_type oloc lrt = 
    let@ l = get () in
    set (L.bind_logical oloc l lrt)

  let logically_bind_return_type oloc rt = 
    let@ l = get () in
    let ((bt, s), l') = L.bind_logically oloc l rt in
    let@ () = set l' in
    return (bt, s)


end
