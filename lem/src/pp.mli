open Format
val pp_str : formatter -> string -> unit

val lst : ('a, formatter, unit) format -> (formatter -> 'b -> unit) -> formatter -> 'b list -> unit

val opt : (formatter -> 'a -> unit) -> formatter -> 'a option -> unit

val pp_to_string : (formatter -> 'a) -> string
