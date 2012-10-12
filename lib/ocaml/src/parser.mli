open Pervasives

module type PARSER_BASE = sig
  exception Error
  type result
  type token

  val init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> result
end


module CparserBase : (PARSER_BASE with type token  = Cparser.token
                                  and  type result = Cabs.g_defn_l list)

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

module MakeParser : MAKE_PARSER

module Cparser : module type of (MakeParser (CparserBase) (Lexer.Clexer))
