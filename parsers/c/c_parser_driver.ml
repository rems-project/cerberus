open Cerb_frontend

(* DIRTY hack to fix col positions when seing a CN keyword *)
(* obviously this messes-up the col positions when using __cerb_{CN_keyword} directly *)
let lexer_cn_hack lexbuf =
  let open Lexing in
  if !C_lexer.inside_cn then
    let tok = C_lexer.lexer lexbuf in
    let pos_cnum' = lexbuf.lex_start_p.pos_cnum + !C_lexer.cnum_hack in
    (* this should never fail, but better being careful ... *)
    if pos_cnum' - lexbuf.lex_start_p.pos_bol >= 0 then
      lexbuf.lex_start_p <- {lexbuf.lex_start_p with pos_cnum= lexbuf.lex_start_p.pos_cnum + !C_lexer.cnum_hack };
    begin match tok with
      | Tokens.CN_PREDICATE ->
          (* removing the length of "__cerb_" *)
          C_lexer.cnum_hack := !C_lexer.cnum_hack - 7
      | _ ->
          ()
    end;
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_cnum= lexbuf.lex_curr_p.pos_cnum + !C_lexer.cnum_hack };
    tok
  else
    C_lexer.lexer lexbuf

let parse lexbuf =
  try
    Exception.except_return @@ C_parser.translation_unit lexer_cn_hack lexbuf
  with
  | C_lexer.Error err ->
    let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error ->
    let loc = Location_ocaml.(region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) NoCursor) in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token (Lexing.lexeme lexbuf)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
    failwith @@ "CPARSER_DRIVER(" ^ Location_ocaml.location_to_string loc ^ ")" ^ " ==> " ^ Stdlib.Printexc.to_string exn

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
