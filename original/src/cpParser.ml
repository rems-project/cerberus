open CpPervasives

let parse lexer =
  try
    let name = CpLexer.name lexer in
    CpLexer.lexbuf (Frontc.parse_exn name) lexer
  with Errormsg.Error ->
    let msg = "The C parser reported an error." in
    raise_error msg

