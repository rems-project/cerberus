open Global

type token_stream = unit -> Cparser.token

type t = {
  name : string;
  lexbuf : 'a. (Lexing.lexbuf -> 'a) -> 'a;
  stream : 'a. (token_stream  -> 'a) -> 'a
}

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
    Input.read (f -| fname name -| BatLexing.from_input) input in
  let stream f =
    let to_stream lexbuf =
      fun () -> Clexer.initial lexbuf in
    Input.read (f -| to_stream -| fname name -| BatLexing.from_input) input in
  {name; lexbuf; stream}
