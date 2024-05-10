open Cerb_frontend

let after_before_msg offset buffer (lexbuf : Lexing.lexbuf) =
  MenhirLib.ErrorReports.show (fun (start, curr) ->
   try Lexing.lexeme {
     lexbuf with
     lex_start_pos = start.Lexing.pos_cnum - offset;
     lex_curr_pos = curr.Lexing.pos_cnum - offset;
   }
   with Invalid_argument _ ->
       Printf.sprintf "CPARSER_DRIVER(lex_buffer_len = %d; offset = %d; start_index = %d; end_index = %d)"
          lexbuf.lex_buffer_len offset (start.pos_cnum - offset) (curr.pos_cnum - offset)
    ) buffer

let handle parse (token_pos_buffer, lexer) ~offset lexbuf =
  try Exception.except_return (parse lexer lexbuf) with
  | C_lexer.Error err ->
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error state ->
    let message =
      try
        let msg = C_parser_error.message state in
        if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n" then raise Not_found else msg
      with Not_found ->
        Printf.sprintf "Please add error message for state %d to parsers/c/c_parser_error.messages\n" state
    in
    let message = String.sub message 0 (String.length message - 1) in
    let (start_p, end_p) = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let loc = Cerb_location.(region (start_p, end_p) NoCursor) in
    let where = after_before_msg offset token_pos_buffer lexbuf in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token  (where ^ "\n" ^ message)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    failwith @@ "CPARSER_DRIVER(" ^ Cerb_location.location_to_string loc ^ ")" ^ " ==> " ^ Stdlib.Printexc.to_string exn

let parse_with_magic_comments lexbuf =
  handle
    C_parser.translation_unit
    (MenhirLib.ErrorReports.wrap (C_lexer.lexer ~inside_cn:false))
    ~offset:0
    lexbuf

let start_pos loc =
  let open Cerb_location in
  match to_raw loc with
  | Loc_point loc
  | Loc_region (loc, _, _)
  | Loc_regions ((loc, _) :: _, _) -> Some loc
  | _ -> None

let magic_comments_to_cn (Cabs.TUnit decls) =
  let convert_toplevel_magic = function
    | Cabs.EDecl_magic (loc, str) ->
      let lexbuf = Lexing.from_string str in
      let start_pos = Option.get @@ start_pos loc in
      Lexing.set_position lexbuf start_pos;
      Lexing.set_filename lexbuf (Option.value ~default:"<none>" (Cerb_location.get_filename loc));
      handle
        C_parser.cn_toplevel
        (MenhirLib.ErrorReports.wrap (C_lexer.lexer ~inside_cn:true))
        ~offset:start_pos.pos_cnum
        lexbuf
    | decl -> Exception.except_return [decl] in

  let decls = Exception.except_mapM convert_toplevel_magic decls in
  let decls = Exception.except_fmap List.concat decls in
  Exception.except_bind decls (fun decls ->
    Exception.except_return (Cabs.TUnit decls))

let parse lexbuf =
  Exception.except_bind (parse_with_magic_comments lexbuf)
    magic_comments_to_cn

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
