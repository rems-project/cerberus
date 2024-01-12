open Cerb_frontend

let warn_toplevel_deprecated loc = prerr_endline (Pp_utils.to_plain_pretty_string (
  let open Cerb_pp_prelude in
  let open Cerb_colour in
  pp_ansi_format [Bold; Yellow] (fun () -> !^ "warning:") ^^^
  !^ "deprecated CN declaration: use /*@ @*/ comment:" ^^ PPrint.break 1 ^^^
  Cerb_location.pp_location ~clever:false loc))

let loc_region_to_range loc = match Cerb_location.to_raw loc with
  | Cerb_location.Loc_region (start_pos, end_pos, _) ->
    Some (start_pos, end_pos)
  | _ -> None

let mk_lexbuf_from_loc_strs loc_strs =
  let data_ref = ref (None, loc_strs) in
  let buf_ref = ref (Lexing.from_string "default") in
  let rec refill bs sz = match ! data_ref with
    | (None, []) -> 0
    | (Some s, loc_strs) ->
      let (len, rem) = if String.length s <= sz
        then (String.length s, None)
        else (sz, Some (String.sub s sz (String.length s - sz)))
      in
      Bytes.blit_string s 0 bs 0 len;
      data_ref := (rem, loc_strs);
      len
    | (None, ((loc, str) :: loc_strs)) ->
      begin match loc_region_to_range loc with
        | Some (start, _) -> begin
          Lexing.set_filename (! buf_ref) (Lexing.(start.pos_fname));
          Lexing.set_position (! buf_ref) start
        end
        | _ -> ()
      end;
      data_ref := (Some str, loc_strs);
      refill bs sz
  in
  let lexbuf = Lexing.from_function ~with_positions:true refill in
  buf_ref := lexbuf;
  lexbuf

let snippet_from_loc_strs loc_strs (l_pos, r_pos) =
  let open Lexing in
  let l_cn = l_pos.pos_cnum in
  let r_cn = r_pos.pos_cnum in
  let r = List.filter_map (fun (loc, s) -> match loc_region_to_range loc with
    | Some (l_pos2, r_pos2) ->
        if l_pos2.pos_cnum <= l_cn && r_cn <= r_pos2.pos_cnum
          && String.length s >= (r_cn - l_pos2.pos_cnum)
        then Some (String.sub s (l_cn - l_pos2.pos_cnum) (r_cn - l_cn))
        else None
    | _ -> None
  ) loc_strs in
  match r with
    | [] -> ("(loc-range not found in source)")
    | (s :: _)  -> s

let snippet_from_lexbuf lexbuf (l_pos, r_pos) =
  let open Lexing in
  let l_cn = l_pos.pos_cnum in
  let r_cn = r_pos.pos_cnum in
  if l_cn < lexbuf.lex_buffer_len && r_cn <= lexbuf.lex_buffer_len
  then
    Lexing.lexeme {
        lexbuf with
        lex_curr_pos = l_cn;
        lex_start_pos = r_cn;
      }
  else (
    Printf.sprintf "CPARSER_DRIVER(lex_buffer_len = %d; l_cnum = %d; r_cnum = %d)"
      lexbuf.lex_buffer_len l_cn r_cn
  )

let after_before_msg get_snippet buffer = try
  MenhirLib.ErrorReports.show get_snippet buffer
  with Invalid_argument _ -> "(error formatting 'where' information)"

let parse_exception parse lexer get_snippet lexbuf =
  let c_buffer, c_lexer = MenhirLib.ErrorReports.wrap lexer in
  try
    Exception.except_return (parse c_lexer lexbuf)
  with
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
    let pos_range = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let loc = Cerb_location.(region pos_range NoCursor) in
    let where = after_before_msg get_snippet c_buffer in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token (where ^ "\n" ^ message)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
    failwith @@ "CPARSER_DRIVER(" ^ Cerb_location.location_to_string loc ^ ")" ^ " ==> " ^ Stdlib.Printexc.to_string exn

let convert_toplevel_magic = function
  | Cabs.EDecl_magic (loc, loc_strs) ->
    let lexbuf = mk_lexbuf_from_loc_strs loc_strs in
    let get_snippet = snippet_from_loc_strs loc_strs in
    parse_exception C_parser.cn_toplevel (C_lexer.cn_lexer ()) get_snippet lexbuf
  | EDecl_predCN _
  | EDecl_funcCN _
  | EDecl_lemmaCN _
  | EDecl_datatypeCN _ as decl ->
    (warn_toplevel_deprecated (Cabs.loc_of_edecl decl);
     Exception.except_return [decl])
  | decl -> Exception.except_return [decl]

let parse_with_cn lexbuf =
  let get_snippet = snippet_from_lexbuf lexbuf in
  Exception.except_bind
    (parse_exception C_parser.translation_unit C_lexer.lexer get_snippet lexbuf)
    (function
      | Cabs.TUnit decls ->
        Exception.except_bind
          (Exception.except_mapM convert_toplevel_magic decls)
          (fun decls2 -> Exception.except_return (Cabs.TUnit (List.concat decls2)))
    )

let parse = parse_with_cn

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
