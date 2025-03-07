open Cerb_frontend
open Core_parser_util

let genparse mode std filename =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
  let module Parser = Core_parser.Make (struct
    let mode = mode
    let std = std
  end) in
  let parse_channel ic =
    let lexbuf = Lexing.from_channel ic in
    (* TODO: I don't know why Lexing is losing the filename information!! *)
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p  with pos_fname= filename };
    let to_pos = Cerb_position.from_lexing in
    try
      Exception.except_return @@ Parser.start Core_lexer.main lexbuf
    with
      | Core_lexer.Error cause ->
          let loc = Cerb_location.point (to_pos (Lexing.lexeme_start_p lexbuf)) in
          Exception.fail (loc, Errors.(CORE_PARSER (Core_lexer cause)))
      | Parser.Error ->
          let loc = Cerb_location.(region (to_pos (Lexing.lexeme_start_p lexbuf), to_pos (Lexing.lexeme_end_p lexbuf)) NoCursor) in
          Exception.fail (loc, Errors.(CORE_PARSER (Core_parser_unexpected_token (Lexing.lexeme lexbuf))))
      | Core_parser_util.Core_error (loc, err) ->
          Exception.fail (loc, Errors.CORE_PARSER err)
      | exn ->
          let loc = Cerb_location.point (to_pos (Lexing.lexeme_start_p lexbuf)) in
          let str = Printf.sprintf "[uncaught exception] '%s'" (String.escaped (Printexc.to_string_default exn)) in
          Exception.fail (loc, Errors.(CORE_PARSER (Core_parser_internal_error str)))
  in
  read parse_channel filename

let parse_stdlib =
  genparse StdMode (Pmap.empty _sym_compare)

let parse stdlib =
  genparse ImplORFileMode
    begin List.fold_left (fun acc (fsym, _) ->
        let open Symbol in
        let Symbol (_, _, sd) = fsym in
        match sd with
        | SD_Id str ->
          let std_pos = Cerb_position.from_lexing {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        | SD_unnamed_tag _
        | SD_CN_Id _
        | SD_ObjectAddress _
        | SD_Return
        | SD_FunArg _
        | SD_FunArgValue _
        (* | SD_Pointee _ *)
        (* | SD_PredOutput _ *)
        | SD_None ->
          acc
      ) (Pmap.empty Core_parser_util._sym_compare) (Pmap.bindings_list (snd stdlib))
    end
