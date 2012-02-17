type t
val read : (BatIO.input -> 'a) -> t -> 'a
val name : t -> string

val file : string -> t
