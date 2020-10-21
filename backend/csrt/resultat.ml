include Result


let return (a: 'a) : ('a,'e) t = 
  Ok a

let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * TypeErrors.stacktrace option * 'e) t = 
  Error (loc, TypeErrors.do_stack_trace (),  e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind

type 'a m = ('a, Locations.t * TypeErrors.stacktrace option * TypeErrors.t) t


(* let actionM level pp = return (Pp.action level pp)
 * let printM level pp = let () = Pp.print level pp in return ()
 * let warnM pp = let () = Pp.warn pp in return () *)



