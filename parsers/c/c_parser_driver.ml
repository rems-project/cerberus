open Cerb_frontend

(* DIRTY hack to fix col positions when seing a CN keyword *)
(* obviously this messes-up the col positions when using __cerb_{CN_keyword} directly *)
let lexer_cn_hack ~c_lexer lexbuf =
  let open Lexing in
  if C_lexer.internal_state.inside_cn then
    let tok = c_lexer lexbuf in
    let pos_cnum' = lexbuf.lex_start_p.pos_cnum + C_lexer.internal_state.cnum_hack in
    (* this should never fail, but better being careful ... *)
    if pos_cnum' - lexbuf.lex_start_p.pos_bol >= 0 then
      lexbuf.lex_start_p <- {lexbuf.lex_start_p with pos_cnum=pos_cnum' };
    begin match tok with
      | Tokens.CN_PREDICATE ->
          (* removing the length of "__cerb_" *)
          C_lexer.internal_state.cnum_hack <- C_lexer.internal_state.cnum_hack - 7
      | _ ->
          ()
    end;
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_cnum= lexbuf.lex_curr_p.pos_cnum + C_lexer.internal_state.cnum_hack };
    tok
  else
    c_lexer lexbuf

let warn_toplevel_deprecated loc = prerr_endline (Pp_utils.to_plain_pretty_string (
  let open Cerb_pp_prelude in
  let open Cerb_colour in
  pp_ansi_format [Bold; Yellow] (fun () -> !^ "warning:") ^^^
  !^ "deprecated CN declaration: use /*@ @*/ comment:" ^^ PPrint.break 1 ^^^
  Cerb_location.pp_location ~clever:false loc))

let most_recent_lexbuf = ref (Lexing.from_string "foo")

let convert_toplevel_magic c_lexer = function
  | Cabs.EDecl_magic (loc, str) ->
    let lexbuf = Lexing.from_string str in
    begin match Cerb_location.to_raw loc with
      | Cerb_location.Loc_region (pos, pos2, _) ->
          (Lexing.set_filename lexbuf (Lexing.(pos.pos_fname));
          Lexing.set_position lexbuf pos)
      | _ -> ()
    end;
    C_lexer.internal_state.inside_cn <- true;
    most_recent_lexbuf := lexbuf;
    C_parser.cn_toplevel c_lexer lexbuf
  | EDecl_predCN _
  | EDecl_funcCN _
  | EDecl_lemmaCN _
  | EDecl_datatypeCN _ as decl ->
    (warn_toplevel_deprecated (Cabs.loc_of_edecl decl);
     [decl])
  | decl -> [decl]

let parse_with_cn ~c_lexer lexbuf =
  let Cabs.TUnit decls = C_parser.translation_unit (lexer_cn_hack ~c_lexer) lexbuf in
  Cabs.TUnit (List.concat (List.map (convert_toplevel_magic c_lexer) decls))

let after_before_msg buffer ~cnum_hack (lexbuf : Lexing.lexbuf) = try
  MenhirLib.ErrorReports.show (fun (start, curr) ->
      let start_pos = start.Lexing.pos_cnum - cnum_hack in
      let curr_pos = curr.Lexing.pos_cnum - cnum_hack in
      if start_pos < lexbuf.lex_buffer_len && curr_pos < lexbuf.lex_buffer_len then
        Lexing.lexeme {
            lexbuf with
            lex_curr_pos = curr_pos;
            lex_start_pos = start_pos;
          }
      else (
        Printf.sprintf "CPARSER_DRIVER(lex_buffer_len = %d; start_pos = %d; curr_pos = %d; cnum_hack = %d)"
          lexbuf.lex_buffer_len start_pos curr_pos cnum_hack;
      )
    ) buffer
  with Invalid_argument _ -> "(error formatting 'where' information)"

let parse lexbuf =
  let c_buffer, c_lexer = MenhirLib.ErrorReports.wrap C_lexer.lexer in
  try
    most_recent_lexbuf := lexbuf;
    Exception.except_return (parse_with_cn ~c_lexer lexbuf)
  with
  | C_lexer.Error err ->
    let lexbuf = ! most_recent_lexbuf in
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error state ->
    let lexbuf = ! most_recent_lexbuf in
    let message =
      try
        let msg = C_parser_error.message state in
        if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n" then raise Not_found else msg
      with Not_found ->
        Printf.sprintf "Please add error message for state %d to parsers/c/c_parser_error.messages\n" state
    in
    let message = String.sub message 0 (String.length message - 1) in
    let tok = Lexing.lexeme lexbuf in
    let cnum_hack = lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_pos in
    assert (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_pos = cnum_hack);
    let (tok_str, start_p, end_p) =
      if String.equal tok "*/"
        then ("(magic comment)", C_lexer.internal_state.start_of_comment, Lexing.lexeme_end_p lexbuf)
        else (tok, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
    in
    let loc = Cerb_location.(region (start_p, end_p) NoCursor) in
    let where = after_before_msg ~cnum_hack c_buffer lexbuf in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token  (where ^ "\n" ^ message)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let lexbuf = ! most_recent_lexbuf in
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
