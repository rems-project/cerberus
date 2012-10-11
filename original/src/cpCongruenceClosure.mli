type t

type constant = int
type apply = constant * constant
type term =
  | Constant of constant
  | Apply of apply

val create : int -> t

val merge : t -> term -> constant -> t
val merge_constants : t -> constant -> constant -> t
val normalise : t -> term -> term
val normalise_constant : t -> constant -> constant
val congruent : t -> term -> term -> bool
val congruent_constants : t -> constant -> constant -> bool

val size : t -> int

val grow : t -> int -> t
