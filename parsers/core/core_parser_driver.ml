open Prelude
open Core_parser_util

let genparse sym_counter mode std filename =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
  let module Parser = Core_parser.Make (struct
    let sym_counter = sym_counter
    let mode = mode
    let std = std
  end) in
  let parse_channel ic =
    let lexbuf = Lexing.from_channel ic in
    (* TODO: I don't know why Lexing is losing the filename information!! *)
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p  with pos_fname= filename };
    try
      Exception.except_return @@ Parser.start Core_lexer.main lexbuf
    with
    | Core_lexer.Error ->
      let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
      Exception.fail (loc, Errors.CORE_PARSER Errors.Core_parser_invalid_symbol)
    | Parser.Error ->
      let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
      Exception.fail (loc, Errors.CORE_PARSER (Errors.Core_parser_unexpected_token (Lexing.lexeme lexbuf)))
    | Core_parser_util.Core_error err ->
      (* TODO: Location information is wrong! *)
      let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
      Exception.fail (loc, Errors.CORE_PARSER err)
    | Failure msg ->
      prerr_endline "CORE_PARSER_DRIVER (Failure)";
      failwith msg
    | _ ->
      failwith "CORE_PARSER_DRIVER"
  in
  read parse_channel filename

let parse_stdlib sym_counter =
  genparse sym_counter StdMode (Pmap.empty _sym_compare)

let parse sym_counter stdlib =
  genparse sym_counter ImplORFileMode
    begin List.fold_left (fun acc (fsym, _) ->
        match fsym with
        | Symbol.Symbol (_, Some str) ->
          let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        | Symbol.Symbol (_, None) ->
          acc
      ) (Pmap.empty Core_parser_util._sym_compare) (Pmap.bindings_list (snd stdlib))
    end
