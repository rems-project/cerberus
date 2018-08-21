let parse input =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
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
      prerr_endline "CORE_PARSER_DRIVER (Failure)";
      failwith msg
    | _ ->
      failwith "CORE_PARSER_DRIVER"
  in
  read parse_channel input
