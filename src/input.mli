type t
type input = in_channel

val read : (input -> 'a) -> t -> 'a
val name : t -> string

val check_suffix: t -> string -> bool

val file : string -> t
