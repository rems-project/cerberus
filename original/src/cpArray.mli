type 'a t

val init : int -> (int -> 'a) -> 'a t
val create : int -> 'a -> 'a t
val get : 'a t -> int -> 'a
val set : 'a t -> int -> 'a -> 'a t
val update : 'a t -> int -> ('a -> 'a) -> 'a t

module Growable : sig
  type 'a t

  val init : int -> (int -> 'a) -> 'a t
  val create : int -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val set : 'a t -> int -> 'a -> 'a t
  val update : 'a t -> int -> ('a -> 'a) -> 'a t
  val grow : 'a t -> int -> (int -> 'a) -> 'a t
  val size : 'a t -> int
end
