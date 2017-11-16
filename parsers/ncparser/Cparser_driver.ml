open Parser
open Tokens

module M = Map.Make (struct
  type t = string
  let compare = Pervasives.compare
end)

let parse input =
  let parse_channel ic =
    let lexbuf = Lexing.from_channel ic in
    let fail lexbuf =
      let cause = Errors.Cparser_cause
          (Errors.Cparser_unexpectedToken (Lexing.lexeme lexbuf))
      in
      let loc = Lexing.lexeme_start_p lexbuf |> Location_ocaml.point in
      Exception.fail (loc, cause)
    in
    try
      Parser.translation_unit Lexer.lexer lexbuf
      |> Exception.except_return
    with
    | Failure msg ->
      prerr_endline "DEBUG: CPARSER_DRIVER, Failure";
      failwith msg
    | Lexer.NonStandard_string_concatenation ->
      prerr_endline "ERROR: unsupported non-standard concatenation of \
                     string literals";
      fail lexbuf
    | _ ->
      fail lexbuf
  in
  Input.read parse_channel input
