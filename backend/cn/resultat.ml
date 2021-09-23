(* include Result *)
module Loc = Locations

type ('a, 'e) t =  ('a, 'e) Result.t
type ('a, 'e) m = ('a, 'e) t


let return (a: 'a) : ('a,'e) t = 
  Ok a

let fail (e: 'e) : ('a, 'e) t = 
  Error e

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let@) = bind



