type t
type set

val make : unit -> set

val count : set -> int

val fresh : set -> t
val fresh_name : set -> string -> t

val to_string : t -> string
val to_string_pretty : t -> string
val to_string_latex : t -> string
val to_string_id : t -> string
