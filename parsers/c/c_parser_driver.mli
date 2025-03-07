
(** Run only the lexer on a given string.
The result is (token string, (line,column))
XXX: It might be nice to generalize this to show both source and file locs.
*)
val diagnostic_get_tokens :
  inside_cn:bool ->
  Cerb_location.t -> string -> string list * (int * int) list


(** Parse something in CN.
The first argument is the thing we are parsing,
the second one is a located string that needs to be parsed. *)
val parse_loc_string :
  ((Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> 'a) ->
  Cerb_location.t * string ->
  ('a, Cerb_location.t * Cerb_frontend.Errors.cause)
  Cerb_frontend.Exception.exceptM


(** Parse a C translation unit from a file.
The first argument is the name of the file to parse. *)
val parse_from_channel :
  string ->
  (Cerb_frontend.Cabs.translation_unit,
   Cerb_location.t * Cerb_frontend.Errors.cause)
  Cerb_frontend.Exception.exceptM


(** Parse a C translation unit from the given string.

When working with a pre-processed file, the name should be the
name of the preprocessed file.  The original source name can be recovered
from the pre-processing annotations.
*)
val parse_from_string :
  filename:string ->
  string ->
  (Cerb_frontend.Cabs.translation_unit,
   Cerb_location.t * Cerb_frontend.Errors.cause)
  Cerb_frontend.Exception.exceptM
