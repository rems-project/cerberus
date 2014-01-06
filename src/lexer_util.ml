open Global

let (-|) f g x = f (g x)

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

module Make (B : BASE) : (LEXER with type token = B.token) = struct
  type token = B.token
  type token_stream = unit -> token

  type t = {
    lexbuf : 'a. (Lexing.lexbuf -> 'a) -> 'a;
    stream : 'a. (token_stream  -> 'a) -> 'a
  }

  let main = B.main

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
	fun () -> B.main lexbuf in
      Input.read (f -| to_stream -| fname name -| Lexing.from_channel) input in
    {lexbuf; stream}
end
