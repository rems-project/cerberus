module type Config = sig
  val warn_extra_semicolon : bool
end

module Make(Conf: Config) : sig

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
  ('a, Cerb_location.t * Cerb_frontend.Errors.cause) Result.t


(** Parse a C translation unit from a file.
The first argument is the name of the file to parse. *)
val parse_from_channel :
  string ->
  ( Cerb_frontend.Cabs.translation_unit
  , Cerb_location.t * Cerb_frontend.Errors.cause ) Result.t


(** Parse a C translation unit from the given string.

When working with a pre-processed file, the name should be the
name of the preprocessed file.  The original source name can be recovered
from the pre-processing annotations.
*)
val parse_from_string :
  filename:string ->
  string ->
  ( Cerb_frontend.Cabs.translation_unit
  , Cerb_location.t * Cerb_frontend.Errors.cause ) Result.t

module C_parser : sig
  open Cerb_frontend
  type token = Tokens.token

  exception Error of int

  val translation_unit :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    Cabs.translation_unit

  val loop_spec :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    (Symbol.identifier, Cabs.type_name) Cn.cn_loop_spec

  val fundef_spec :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    (Symbol.identifier, Cabs.type_name) Cn.cn_func_spec

  val cn_toplevel :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    Cabs.external_declaration list

  val cn_statements :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    (Symbol.identifier, Cabs.type_name) Cn.cn_statement list

  val cn_ghost_args :
    (Lexing.lexbuf -> token) ->
    Lexing.lexbuf ->
    (Symbol.identifier, Cabs.type_name) Cn.cn_expr list
    * Symbol.identifier list
end
end