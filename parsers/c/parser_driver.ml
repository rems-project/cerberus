open Cerb_frontend

let after_before_msg offset buffer (lexbuf : Lexing.lexbuf) =
  let show_token (start, curr) =
    try
      Lexing.lexeme {
        lexbuf with
        lex_start_pos = start.Lexing.pos_cnum - offset;
        lex_curr_pos = curr.Lexing.pos_cnum - offset;
      }
    with Invalid_argument _ ->
      Printf.sprintf
        "CPARSER_DRIVER(lex_buffer_len = %d; offset = %d; start_index = %d; end_index = %d)"
        lexbuf.lex_buffer_len
        offset
        (start.pos_cnum - offset)
        (curr.pos_cnum - offset) in
  MenhirLib.ErrorReports.show show_token buffer

module Make(M: sig
  type cause
  type token
  exception Lexer_error of cause
  exception Parser_error of int
  val message_file : string
  val unexpected_token : string -> Errors.cause
  val lift_cause : cause -> Errors.cause
  val error_message : int -> string
end) = struct
  let handle parse (token_pos_buffer, lexer) ~offset lexbuf =
    try Result.ok (parse lexer lexbuf) with
    | M.Lexer_error err ->
      let loc =
        Cerb_location.point (C_lexer.LineMap.position (Lexing.lexeme_start_p lexbuf)) in
      Result.error (loc, M.lift_cause err)
    | M.Parser_error state ->
      let message =
        try
          let msg = M.error_message state in
          if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n"
            then raise Not_found else msg
        with Not_found ->
          Printf.sprintf "Please add error message for state %d to parsers/c/%s\n"
            state M.message_file
      in
      let message = String.sub message 0 (String.length message - 1) in
      let range =
        ( C_lexer.LineMap.position (Lexing.lexeme_start_p lexbuf)
        , C_lexer.LineMap.position (Lexing.lexeme_end_p lexbuf) ) in
      let loc = Cerb_location.(region range NoCursor) in
      let where = after_before_msg offset token_pos_buffer lexbuf in
      Result.error (loc, M.unexpected_token (where ^ "\n" ^ message))
    | Failure msg ->
      prerr_endline "CNPARSER_DRIVER (Failure)";
      failwith msg
    | Lexer_feedback.KnR_declaration loc ->
      Result.error (loc, Errors.C_PARSING Errors.Cparser_KnR_declaration)
    | exn ->
      let loc =
        Cerb_location.point
          @@ Cerb_position.from_lexing @@ Lexing.lexeme_start_p lexbuf in
      failwith @@
        "CNPARSER_DRIVER(" ^ Cerb_location.location_to_string loc ^ ")" ^ " ==> " ^
        Stdlib.Printexc.to_string exn
end
