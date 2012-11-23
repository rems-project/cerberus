module type BASE = sig
  type token
  val main : Lexing.lexbuf -> token
end

module type LEXER = sig
  type token
  type token_stream = unit -> token

  type t

  val main : Lexing.lexbuf -> token

  val lexbuf : (Lexing.lexbuf -> 'a) -> t -> 'a
  val stream : (token_stream -> 'a)  -> t -> 'a

  val make : Input.t -> t
end

module Make (B : BASE) : (LEXER with type token = B.token)
