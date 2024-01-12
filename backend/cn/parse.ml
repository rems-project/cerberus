(* open Cerb_frontend *)
open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Pp
module Cn = Cerb_frontend.Cn


module Loc = Locations

let diagnostic_get_tokens loc_strs =
  let lexbuf = C_parser_driver.mk_lexbuf_from_loc_strs loc_strs in
  let lexer = C_lexer.cn_lexer () in
  let rec f xs = try begin match lexer lexbuf with
    | Tokens.EOF -> List.rev ("EOF" :: xs)
    | t -> f (Tokens.string_of_token t :: xs)
  end with C_lexer.Error err -> List.rev (CF.Pp_errors.string_of_cparser_cause err :: xs)
  in
  f []


(* adapting from core_parser_driver.ml *)

let parse parser_start loc_strs =
  let lexbuf = C_parser_driver.mk_lexbuf_from_loc_strs loc_strs in
  let buffer, lexer = MenhirLib.ErrorReports.wrap (C_lexer.cn_lexer ()) in
  let@ parsed_spec =
    try return (parser_start lexer lexbuf) with
    | C_lexer.Error err ->
       let loc = Cerb_location.point @@ Lexing.lexeme_start_p lexbuf in
       fail {loc; msg = Parser err}
    | C_parser.Error state ->
       let message =
         try
           let msg = C_parser_error.message state in
           if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n" then raise Not_found else msg
         with Not_found ->
           Printf.sprintf "Please add error message for state %d to parsers/c/c_parser_error.messages\n" state
       in
       let message = String.sub message 0 (String.length message - 1) in
       (* the two tokens between which the error occurred *)
       let where = try MenhirLib.ErrorReports.show
           (C_parser_driver.snippet_from_loc_strs loc_strs) buffer
         with Invalid_argument _ -> "(error in fetching token)" in
       let r = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
       let loc = Cerb_location.(region r NoCursor) in
       Pp.debug 6 (lazy (
           let toks = try diagnostic_get_tokens loc_strs
             with C_lexer.Error _ -> ["(re-parse error)"] in
           Pp.item "failed to parse tokens" (Pp.braces (Pp.list Pp.string toks))));
       fail {loc; msg = Parser (Cparser_unexpected_token (where ^ "\n" ^ message))}
  in
  return parsed_spec

let magic_comments_of_attributes (Attrs attributes) =
  List.concat_map (fun attr ->
    (* FIXME (TS): sometimes this needs to be cerb::magic, other times
       cn:... is used. this all feels like a hack *)
    let k = (Option.value ~default:"<>" (Option.map Id.s attr.attr_ns), Id.s attr.attr_id) in
    let use = List.exists (fun (x, y) -> String.equal x (fst k) && String.equal y (snd k))
        [("cerb", "magic"); ("cn", "requires"); ("cn", "ensures");
            ("cn", "accesses"); ("cn", "trusted")] in
    if use
    then List.map (fun (loc, _, loc_strs) -> loc_strs) attr.attr_args
    else []
  ) attributes


let parse_function_spec attributes =
  let@ conditions = ListM.concat_mapM (fun comment ->
      parse C_parser.function_spec comment
   ) (magic_comments_of_attributes attributes) in
  ListM.fold_leftM (fun acc cond ->
    match cond, acc with
    | (Cn.CN_trusted loc), (_, [], [], [], []) ->
       return (Mucore.Trusted loc, [], [], [], [])
    | (Cn.CN_trusted loc), _ ->
       fail {loc; msg= Generic !^"Please specify 'trusted' before other conditions"}
    | (CN_accesses (loc, ids)), (trusted, accs, [], [], ex) ->
       return (trusted, accs @ List.map (fun id -> (loc, id)) ids, [], [], ex)
    | (CN_accesses (loc, _)), _ ->
       fail { loc; msg= Generic !^"Please specify 'accesses' before any 'requires' and 'ensures'" }
    | (CN_requires (loc, cond)), (trusted, accs, reqs, [], ex) ->
       return (trusted, accs, reqs @ List.map (fun c -> (loc, c)) cond, [], ex)
    | (CN_requires (loc, _)), _ ->
       fail {loc; msg = Generic !^"Please specify 'requires' before any 'ensures'"}
    | (CN_ensures (loc, cond)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss @ List.map (fun c -> (loc, c)) cond, ex)
    | (CN_mk_function (loc, nm)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss, ex @ [(loc, Mucore.Make_Logical_Function nm)])
    )
    (Mucore.Checked, [], [], [], []) conditions

let parse_inv_spec attributes =
  ListM.concat_mapM (fun comment ->
    let@ (Cn.CN_inv (_loc, conds)) = parse C_parser.loop_spec comment in
    return conds
  ) (magic_comments_of_attributes attributes)


