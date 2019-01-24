let parse lexbuf =
  try
    Exception.except_return @@ Parser.translation_unit Lexer.lexer lexbuf
  with
  | Lexer.Error err ->
    let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | Parser.Error ->
    let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token (Lexing.lexeme lexbuf)))
  | Failure "lexing: empty token" ->
    (* NOTE: this is thrown by any error using Lexing.from_string *)
    exit 127
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | _ ->
    failwith "CPARSER_DRIVER"

let parse_from_channel input =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
  let parse_channel ic = parse @@ Lexing.from_channel ic in
  read parse_channel input

let parse_from_string str =
  parse @@ Lexing.from_string str
