type t

type hint = Less of int * int | Equal

val create : int -> t
val find : t -> int -> int
val union : t -> int -> int -> t
val union_hint : t -> int -> int -> t * hint

module Growable : sig
  type hint = Less of int * int | Equal
  type t

  val create : int -> t
  val find : t -> int -> int
  val union : t -> int -> int -> t
  val union_hint : t -> int -> int -> t * hint
  val grow : t -> int -> t
end
