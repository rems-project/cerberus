open Pervasives

module type BASE = sig
  exception Error
  type result
  type token

  val start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> result
end

module type PARSER =
sig
  type result
  val parse : Input.t -> (result, Errors.t9) Exception.t2
end

module type MAKE =
  functor (B : BASE) ->
  functor (L : Lexer_util.LEXER with type token = B.token) ->
    PARSER with type result = B.result

module Make : MAKE
