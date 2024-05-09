open Cerb_frontend

let warn_toplevel_deprecated loc = prerr_endline (Pp_utils.to_plain_pretty_string (
  let open Cerb_pp_prelude in
  let open Cerb_colour in
  pp_ansi_format [Bold; Yellow] (fun () -> !^ "warning:") ^^^
  !^ "deprecated CN declaration: use /*@ @*/ comment:" ^^ PPrint.break 1 ^^^
  Cerb_location.pp_location ~clever:false loc))

let most_recent =
  ref (Lexing.from_string "", fst (MenhirLib.ErrorReports.wrap C_lexer.lexer))

let convert_toplevel_magic = function
  | Cabs.EDecl_magic (loc, str) ->
    let lexbuf = Lexing.from_string str in
    begin match Cerb_location.to_raw loc with
      | Cerb_location.Loc_region (pos, pos2, _) ->
          (Lexing.set_filename lexbuf (Lexing.(pos.pos_fname));
          Lexing.set_position lexbuf pos)
      | _ -> ()
    end;
    C_lexer.internal_state.inside_cn <- true;
    let cn_err_buffer, cn_lexer = MenhirLib.ErrorReports.wrap C_lexer.lexer in
    most_recent := (lexbuf, cn_err_buffer);
    C_parser.cn_toplevel cn_lexer lexbuf
  | EDecl_predCN _
  | EDecl_funcCN _
  | EDecl_lemmaCN _
  | EDecl_datatypeCN _ as decl ->
    (warn_toplevel_deprecated (Cabs.loc_of_edecl decl);
     [decl])
  | decl -> [decl]

let parse_with_cn ~c_lexer lexbuf =
  let Cabs.TUnit decls = C_parser.translation_unit c_lexer lexbuf in
  Cabs.TUnit (List.concat (List.map convert_toplevel_magic decls))

let after_before_msg offset buffer (lexbuf : Lexing.lexbuf) =
  MenhirLib.ErrorReports.show (fun (start, curr) ->
   try Lexing.lexeme {
     lexbuf with
     lex_start_pos = start.Lexing.pos_cnum - offset;
     lex_curr_pos = curr.Lexing.pos_cnum - offset;
   }
   with Invalid_argument _ ->
       Printf.sprintf "CPARSER_DRIVER(lex_buffer_len = %d; offset = %d; start.pos_cnum = %d; curr.pos_cnum = %d)"
          lexbuf.lex_buffer_len offset (start.pos_cnum - offset) (curr.pos_cnum - offset)
    ) buffer

let parse lexbuf =
  let c_err_buffer, c_lexer = MenhirLib.ErrorReports.wrap C_lexer.lexer in
  try
    most_recent := (lexbuf, c_err_buffer);
    Exception.except_return (parse_with_cn ~c_lexer lexbuf)
  with
  | C_lexer.Error err ->
    let lexbuf, _ = ! most_recent in
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error state ->
    let lexbuf, buffer = ! most_recent in
    let message =
      try
        let msg = C_parser_error.message state in
        if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n" then raise Not_found else msg
      with Not_found ->
        Printf.sprintf "Please add error message for state %d to parsers/c/c_parser_error.messages\n" state
    in
    let message = String.sub message 0 (String.length message - 1) in
    let (offset, start_p, end_p) =
      if C_lexer.internal_state.inside_cn then
        let start_p =  C_lexer.internal_state.start_of_comment in
        (start_p.pos_cnum + 3, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
      else
        (0, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
    in
    let loc = Cerb_location.(region (start_p, end_p) NoCursor) in
    let where = after_before_msg offset buffer lexbuf in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token  (where ^ "\n" ^ message)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let lexbuf, _ = ! most_recent in
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    failwith @@ "CPARSER_DRIVER(" ^ Cerb_location.location_to_string loc ^ ")" ^ " ==> " ^ Stdlib.Printexc.to_string exn

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
