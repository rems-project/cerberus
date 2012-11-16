type t
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val nth : int -> t
val from_rope : Ulib.Text.t -> t
val to_rope : t -> Ulib.Text.t
