open Cerb_frontend

(** Run only the lexer on a given string.
The result is (token string, (line,column))
XXX: It might be nice to generalize this to show both source and file locs.
*)
val diagnostic_get_tokens :
  Cerb_location.t -> string -> string list * (int * int) list

(** Parse something in CN.
The first argument is the thing we are parsing,
the second one is a located string that needs to be parsed. *)
val parse_loc_string :
  ((Lexing.lexbuf -> Cn_tokens.token) -> Lexing.lexbuf -> 'a) ->
  Cerb_location.t * string ->
  ('a, Cerb_location.t * Errors.cause) Result.t

val magic_comments_to_cn_toplevel :
  Cabs.translation_unit ->
  (Cabs.translation_unit, Cerb_location.t * Errors.cause) result