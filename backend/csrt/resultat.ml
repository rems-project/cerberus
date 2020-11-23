include Result



let return (a: 'a) : ('a,'e) t = 
  Ok a

let error (e: 'e) : ('a,'e) t = 
  Error e

type 'e error = Locations.loc * Tools.stacktrace option * 'e

let fail (loc: Locations.loc) (e: 'e) : ('a, 'e error) t = 
  error (loc, Tools.do_stack_trace (),  e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind



type ('a,'e) m = ('a, 'e error) Result.t


let lift_error (f : 'e1 -> 'e2) (m : ('a,'e1) m) : ('a,'e2) m =
  match m with
  | Ok a -> Ok a
  | Error (loc, stacktrace, e1) -> 
     Error (loc, stacktrace, f e1)


let msum (m1 : ('a,'e) t) (m2 : ('a,'e) t) : ('a,'e) t = 
  match m1 with
  | Ok a -> Ok a
  | Error _ -> m2







let assoc_err loc equality entry list err =
  match List.assoc_opt equality entry list with
  | Some result -> return result
  | None -> fail loc err




