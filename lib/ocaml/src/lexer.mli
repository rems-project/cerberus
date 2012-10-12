module type LEXER_BASE = sig
  type token
  val init : Lexing.lexbuf -> token
end
module ClexerBase : (LEXER_BASE with type token = Cparser.token)
module CoreLexerBase : (LEXER_BASE with type token = Core_parser.token)

module type LEXER = sig
  type token
  type token_stream = unit -> token

  type t

  val init : Lexing.lexbuf -> token

  val name : t -> string
  val lexbuf : (Lexing.lexbuf -> 'a) -> t -> 'a
  val stream : (token_stream -> 'a)  -> t -> 'a

  val make : Input.t -> t
end

module MakeLexer (L : LEXER_BASE) : (LEXER with type token = L.token)
module Clexer : (LEXER with type token = ClexerBase.token)
module CoreLexer : (LEXER with type token = CoreLexerBase.token)
