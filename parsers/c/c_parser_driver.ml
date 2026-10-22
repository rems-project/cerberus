open Cerb_frontend

module type Config = sig
  val warn_extra_semicolon : bool
end

module Make(Conf: Config) = struct
  module C_parser = C_parser.Make(Conf)

  let handle parse (token_pos_buffer, lexer) ~offset lexbuf =
    let module M = Parser_driver.Make(struct
      type token = Tokens.token
      type cause = Errors.cparsing_cause
      exception Lexer_error = C_lexer.Error
      exception Parser_error = C_parser.Error
      let message_file = "c_parser_error.messages"
      let unexpected_token str = Errors.(C_PARSING (Cparser_unexpected_token str))
      let lift_cause cause = Errors.C_PARSING cause
      let error_message = C_parser_error.message
    end) in
    M.handle parse (token_pos_buffer, lexer) ~offset lexbuf

  let parse_with_magic_comments lexbuf =
    let `LEXER c_lexer = C_lexer.create_lexer () in
    handle
      C_parser.translation_unit
      (MenhirLib.ErrorReports.wrap c_lexer)
      ~offset:0
      lexbuf

  let parse lexbuf =
    (* Setup the lexer's line map *)
    C_lexer.LineMap.init lexbuf.Lexing.lex_curr_p.pos_fname;
    Result.bind (parse_with_magic_comments lexbuf)
      Cn_parser_driver.magic_comments_to_cn_toplevel

  let parse_from_channel input =
    let read f input =
      let channel = open_in input in
      let result  = f channel in
      let ()      = close_in channel in
      result
    in
    let parse_channel ic = parse @@ Lexing.from_channel ic in
    read parse_channel input

  let parse_from_string ~filename str =
    let lexbuf = Lexing.from_string str in
    Lexing.set_filename lexbuf filename;
    parse lexbuf
end
