open Cerb_frontend

let handle parse (token_pos_buffer, lexer) ~offset lexbuf =
  let module M = Parser_driver.Make(struct
    type token = Cn_tokens.token
    type cause = Errors.cnparsing_cause
    exception Lexer_error = Cn_lexer.Error
    exception Parser_error = Cn_parser.Error
    let message_file = "cn_parser_error.messages"
    let unexpected_token str = Errors.(CN_PARSING (Cnlexer_unexpected_token str))
    let lift_cause cause = Errors.CN_PARSING cause
    let error_message = Cn_parser_error.message
  end) in
  M.handle parse (token_pos_buffer, lexer) ~offset lexbuf

let start_pos = function
  | Cerb_location.Loc_point loc
  | Loc_region (loc, _, _)
  | Loc_regions ((loc, _) :: _, _) -> Some loc
  | _ -> None

let diagnostic_get_tokens loc string =
  (* `C_lexer.magic_token' ensures `loc` is a region *)
  let start_pos = Option.get @@ start_pos loc in
  let lexbuf = Lexing.from_string string in
  let rec relex (toks, pos) =
    try
      match Cn_lexer.lexer lexbuf with
      | Cn_tokens.EOF -> (List.rev ("EOF" :: toks), List.rev pos)
      | t ->
        let Lexing.{ pos_lnum; pos_bol; pos_cnum; _ } = lexbuf.lex_start_p in
        let (line, col) =
          (* the first line needs to have columns shifted by /*@ but the rest do not *)
          let col_off = if pos_lnum > 1 then 1 else Cerb_position.column start_pos in
          let fi_pos = Cerb_position.to_file_lexing start_pos in
          (pos_lnum + fi_pos.pos_lnum, col_off + pos_cnum - pos_bol) in
        relex (Cn_tokens.string_of_token t :: toks, (line, col) :: pos)
      with
        Cn_lexer.Error err ->
          (List.rev (Pp_errors.string_of_cnparsing_cause err :: toks), List.rev pos)
  in
  relex ([], [])

let parse_loc_string parse (loc, str) =
  let lexbuf = Lexing.from_string str in
  (* `C_lexer.magic_token' ensures `loc` is a region *)
  let start_pos = Option.get @@ start_pos loc in
  Lexing.set_position lexbuf (Cerb_position.to_file_lexing start_pos);
  Lexing.set_filename lexbuf (Option.value ~default:"<none>" (Cerb_location.get_filename loc));
  handle
    parse
    (MenhirLib.ErrorReports.wrap Cn_lexer.lexer)
    ~offset: (Cerb_position.to_file_lexing start_pos).pos_cnum
    lexbuf

let update_enclosing_region payload_region xs =
  let slash_inclusive_region = match payload_region with
    | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
      (* TODO: adjust CERB_MAGIC and EDecl_magic to carry a record:
         { slash_inclusive_region: Cerb_location.t; payload_region: Cerb_location.t } *)
        Cerb_location.region ( Cerb_position.change_cnum start_pos (-3)
                             , Cerb_position.change_cnum end_pos 2) cursor
    | _ -> assert false (* loc should always be a region *)
  in
  let update_decl_with_enclosing_region = function
    | Cabs.EDecl_funcCN func ->
        Cabs.EDecl_funcCN { func with Cn.cn_func_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_lemmaCN lmma ->
        Cabs.EDecl_lemmaCN { lmma with Cn.cn_lemma_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_predCN pred ->
        Cabs.EDecl_predCN { pred with Cn.cn_pred_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_datatypeCN dt ->
        Cabs.EDecl_datatypeCN { dt with Cn.cn_dt_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_type_synCN ts ->
        Cabs.EDecl_type_synCN { ts with Cn.cn_tysyn_loc= slash_inclusive_region }
    | Cabs.EDecl_fun_specCN spec ->
        Cabs.EDecl_fun_specCN spec
    | _ ->
        (* C_parser.cn_toplevel only returns CN external declarations *)
        assert false
  in
  List.map update_decl_with_enclosing_region xs

let magic_comments_to_cn_toplevel (Cabs.TUnit decls) =
  let magic_comments_to_cn_toplevel = function
    | Cabs.EDecl_magic (loc, str) ->
      parse_loc_string Cn_parser.cn_toplevel (loc, str)
      |> Exception.except_fmap (update_enclosing_region loc)
    | decl ->
      Result.ok [decl] in
  decls
  |> Exception.except_mapM magic_comments_to_cn_toplevel
  |> Exception.except_fmap (fun decls -> Cabs.TUnit (List.concat decls))
