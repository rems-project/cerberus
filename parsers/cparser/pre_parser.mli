(* This exception is raised by the monolithic API functions. *)
exception Error

(* The monolithic API. *)
val translation_unit_file: (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> (unit)

