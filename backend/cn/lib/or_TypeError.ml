(* include Result *)

type 'a t = ('a, TypeErrors.t) Result.t

let return (a : 'a) : 'a t = Ok a

let fail (e : 'e) : 'a t = Error e

let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
  match m with Ok a -> f a | Error e -> Error e


let ( let@ ) = bind
