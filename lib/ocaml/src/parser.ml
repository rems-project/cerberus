open Pervasives_
open Exception.Operators

module type PARSER_BASE = sig
  exception Error
  type token
  type result

  val init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> result
end

module CparserBase = struct
  exception Error = Cparser.Error
  type result = Cabs.g_defn_l list
  type token = Cparser.token

  let init = Cparser.start
end

module CoreParserBase = struct
  exception Error = Core_parser.Error
  type token  = Core_parser.token
  type result = (string * (Core.core_type * (string * Core.core_base_type) list * unit Core.expr)) list

  let init = Core_parser.start
end


module type PARSER = functor (L : Lexer.LEXER) ->
sig
  type result
  val parse : L.t -> (result, Errors.cause) Exception.t
end


module type MAKE_PARSER =
  functor (P : PARSER_BASE) ->
  functor (L : Lexer.LEXER with type token = P.token) ->
  sig
    type result = string * P.result
    val parse : L.t -> (result, Errors.cause) Exception.t
  end

module MakeParser
  (P : PARSER_BASE)
  (L : Lexer.LEXER with type token = P.token) =
struct
  type result = string * P.result

  let parse_exn name lexbuf =
    try
      let result = P.init L.init lexbuf in
      Exception.return (name, result)
    with P.Error ->
      let token = Lexing.lexeme lexbuf in
      Exception.throw (Errors.PARSER ("Unexpected token: " ^ token ^ "."))

  let parse lexer =
    let name = L.name lexer in
    L.lexbuf (parse_exn name) lexer
end

module Cparser = MakeParser (CparserBase) (Lexer.Clexer)
module CoreParser = MakeParser (CoreParserBase) (Lexer.CoreLexer)
