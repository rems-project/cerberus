open Cerb_frontend

(* DIRTY hack to fix col positions when seing a CN keyword *)
(* obviously this messes-up the col positions when using __cerb_{CN_keyword} directly *)
let lexer_cn_hack lexbuf =
  let open Lexing in
  if C_lexer.internal_state.inside_cn then
    let tok = C_lexer.lexer lexbuf in
    let pos_cnum' = lexbuf.lex_start_p.pos_cnum + C_lexer.internal_state.cnum_hack in
    (* this should never fail, but better being careful ... *)
    if pos_cnum' - lexbuf.lex_start_p.pos_bol >= 0 then
      lexbuf.lex_start_p <- {lexbuf.lex_start_p with pos_cnum= lexbuf.lex_start_p.pos_cnum + C_lexer.internal_state.cnum_hack };
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
    C_lexer.lexer lexbuf

let most_recent_lexbuf = ref (Lexing.from_string "foo")

let convert_toplevel_magic = function
  | Cabs.EDecl_magic (loc, str) ->
    let lexbuf = Lexing.from_string str in
    let () = match Cerb_location.to_raw loc with Cerb_location.Loc_region (pos, pos2, _) ->
      Lexing.set_filename lexbuf (Lexing.(pos.pos_fname));
      Lexing.set_position lexbuf pos
      | _ -> ()
    in
    C_lexer.internal_state.inside_cn <- true;
    most_recent_lexbuf := lexbuf;
    C_parser.cn_toplevel C_lexer.lexer lexbuf
  | decl -> [decl]

let parse_with_cn lexbuf =
  let Cabs.TUnit decls = C_parser.translation_unit lexer_cn_hack lexbuf in
  Cabs.TUnit (List.concat (List.map convert_toplevel_magic decls))

let parse lexbuf =
  try
    most_recent_lexbuf := lexbuf;
    Exception.except_return (parse_with_cn lexbuf)
  with
  | C_lexer.Error err ->
    let lexbuf = ! most_recent_lexbuf in
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error ->
    let lexbuf = ! most_recent_lexbuf in
    let tok = Lexing.lexeme lexbuf in
    let (tok_str, start_p, end_p) = if String.equal tok "*/"
      then ("(magic comment)", C_lexer.internal_state.start_of_comment, Lexing.lexeme_end_p lexbuf)
      else (tok, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
    in
    let loc = Cerb_location.(region (start_p, end_p) NoCursor) in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token tok_str))
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
