open Pervasives_

let parse lexer =
  try
    let name = Lexer.name lexer in
    Lexer.lexbuf (Frontc.parse_exn name) lexer
  with Errormsg.Error ->
    let msg = "The C parser reported an error." in
    raise_error msg

