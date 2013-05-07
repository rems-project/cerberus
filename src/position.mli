type t

val make : Lexing.position -> Lexing.position -> t
val from_lexbuf : Lexing.lexbuf -> t

val name : t -> string
val first_char : t -> int
val first_line : t -> int
val first_line_offset : t -> int
val last_char : t -> int
val last_line : t -> int
val last_line_offset : t -> int

val lines_to_string : t -> string
