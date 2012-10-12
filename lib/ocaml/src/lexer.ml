open Global

module type LEXER_BASE = sig
  type token
  val init : Lexing.lexbuf -> token
end

module ClexerBase = struct
  type token = Cparser.token
  let init = Clexer.initial
end

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

module MakeLexer (L : LEXER_BASE) : (LEXER with type token = L.token) = struct
  type token = L.token
  type token_stream = unit -> token

  type t = {
    name : string;
    lexbuf : 'a. (Lexing.lexbuf -> 'a) -> 'a;
    stream : 'a. (token_stream  -> 'a) -> 'a
  }

  let init = L.init

  let name {name; _} = name
  let lexbuf f {lexbuf; _} = lexbuf f
  let stream f {stream; _} = stream f

  let fname name lexbuf =
    let open Lexing in
    lexbuf.lex_start_p <- {lexbuf.lex_start_p with pos_fname = name};
    lexbuf.lex_curr_p  <- {lexbuf.lex_curr_p  with pos_fname = name};
    lexbuf

  let make input =
    let name = Input.name input in
    let lexbuf f =
      Input.read (f -| fname name -| Lexing.from_channel) input in
    let stream f =
      let to_stream lexbuf =
	fun () -> L.init lexbuf in
      Input.read (f -| to_stream -| fname name -| Lexing.from_channel) input in
    {name; lexbuf; stream}
end

module Clexer = MakeLexer (ClexerBase)
