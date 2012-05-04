open Pervasives_
open Exception.Operators

let parse_exn name lexbuf =
  try
    let file = Cparser.start Clexer.initial lexbuf in
    Exception.return (name, file)
  with Cparser.Error ->
    let token = Lexing.lexeme lexbuf in
    Exception.throw (Errors.PARSER ("Unexpected token: " ^ token ^ "."))

let parse lexer =
  let name = Lexer.name lexer in
  Lexer.lexbuf (parse_exn name) lexer
