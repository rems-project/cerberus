type t
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val nth : int -> t
val from_rope : BatRope.t -> t
val to_rope : t -> BatRope.t
