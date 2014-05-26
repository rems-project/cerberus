open Pervasives_
open Exception.Operators

module type BASE = sig
  exception Error
  type token
  type result

  val start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> result
end

module type PARSER =
sig
  type result
  val parse : Input.t -> (result, Errors.t8) Exception.t0
end

module type MAKE =
  functor (B : BASE) ->
  functor (L : Lexer_util.LEXER with type token = B.token) ->
    PARSER with type result = B.result


module Make
  (B : BASE)
  (L : Lexer_util.LEXER with type token = B.token) =
struct
  type result = B.result

  let parse_exn lexbuf =
    try
      let result = B.start L.main lexbuf in
      Exception.return0 result
    with B.Error ->
      let token = Lexing.lexeme lexbuf in
      Exception.throw (Location.unknowned, Errors.PARSER ("Unexpected token: " ^ token ^ "."))

  let parse input = L.lexbuf parse_exn (L.make input)
end
