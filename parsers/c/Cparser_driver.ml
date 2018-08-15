let parse input =
  let parse_channel ic =
    let lexbuf = Lexing.from_channel ic in
    try
      Exception.except_return @@ Parser.translation_unit Lexer.lexer lexbuf
    with
    | Lexer.Error err ->
      let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
      Exception.fail (loc, Errors.CPARSER err)
    | Parser.Error ->
      let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
      Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token (Lexing.lexeme lexbuf)))
    | Failure msg ->
      prerr_endline "CPARSER_DRIVER (Failure)";
      failwith msg
    | _ ->
      failwith "CPARSER_DRIVER"
  in
  Input.read parse_channel input
