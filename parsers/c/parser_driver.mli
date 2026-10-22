open Cerb_frontend

module Make (M : sig
  type cause
  type token

  exception Lexer_error of cause
  exception Parser_error of int

  val message_file : string
  val unexpected_token : string -> Errors.cause
  val lift_cause : cause -> Errors.cause
  val error_message : int -> string
end) : sig
  val handle :
    ((Lexing.lexbuf -> M.token) -> Lexing.lexbuf -> 'a) ->
    (Lexing.position * Lexing.position) MenhirLib.ErrorReports.buffer
    * (Lexing.lexbuf -> M.token) ->
    offset:int ->
    Lexing.lexbuf ->
    ('a, Cerb_location.t * Errors.cause) result
end
