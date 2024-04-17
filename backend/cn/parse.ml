(* open Cerb_frontend *)
open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Pp
module Cn = Cerb_frontend.Cn


module Loc = Locations

(* the character @ is not a separator in C, so supporting @start as a
   legacy syntax requires special hacks *)
let fiddle_at_hack string =
  let ss = String.split_on_char '@' string in
  let rec fix = function
    | [] -> ""
    | [s] -> s
    | (s1 :: s2 :: ss) -> if Tools.starts_with "start" s2
        then fix ((s1 ^ "%" ^ s2) :: ss)
        else fix ((s1 ^ "@" ^ s2) :: ss)
  in
  fix ss

let diagnostic_get_tokens (start_pos : Lexing.position) string =
  C_lexer.internal_state.inside_cn <- true;
  let lexbuf = Lexing.from_string string in
  let rec relex (toks, pos) =
    try
      match C_lexer.lexer lexbuf with
      | Tokens.EOF -> (List.rev ("EOF" :: toks), List.rev pos)
      | t ->
        let Lexing.{ pos_lnum; pos_bol; pos_cnum; _ } = lexbuf.lex_start_p in
        let (line, col) =
          (* the first line needs to have columns shifted by /*@ but the rest do not *)
          let col_off = if pos_lnum > 1 then 1 else start_pos.pos_cnum - start_pos.pos_bol + 1 in
          (pos_lnum + start_pos.pos_lnum, col_off + pos_cnum - pos_bol) in
        relex (Tokens.string_of_token t :: toks, (line, col) :: pos)
      with
        C_lexer.Error err ->
          (List.rev (CF.Pp_errors.string_of_cparser_cause err :: toks), List.rev pos)
  in
  relex ([], [])


(* adapting from core_parser_driver.ml *)

let parse parser_start (loc, string) =
  let string = fiddle_at_hack string in
  C_lexer.internal_state.inside_cn <- true;
  let lexbuf = Lexing.from_string string in
  (* `C_lexer.magic_token' ensures `loc` is a region *)
  let start_pos = Option.get @@ Locations.start_pos loc in
  Lexing.set_position lexbuf start_pos;
  let () = match Cerb_location.get_filename loc with
    | Some filename -> lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname= filename }
    | None -> ()
  in
  let buffer, lexer = MenhirLib.ErrorReports.wrap C_lexer.lexer in
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
       let start = Lexing.lexeme_start_p lexbuf in
       let end_ = Lexing.lexeme_end_p lexbuf in
       let loc = Cerb_location.(region (start, end_) NoCursor) in
       (* the two tokens between which the error occurred *)
       let where = MenhirLib.ErrorReports.show (fun (start, curr) ->
           try Lexing.lexeme {
             lexbuf with
             lex_start_pos = start.Lexing.pos_cnum - start_pos.pos_cnum;
             lex_curr_pos = curr.Lexing.pos_cnum - start_pos.pos_cnum;
           }
         with Invalid_argument _ -> "(token_err)"
         ) buffer in
       Pp.debug 6 (lazy (
           let (toks, pos) = diagnostic_get_tokens start_pos string in
           let pp_int_pair (x, y) = Pp.(parens (int x ^^ comma ^^^ int y)) in
           Pp.item "failed to parse tokens" (Pp.braces (Pp.list Pp.string toks))
           ^/^ Pp.item "(line, col)" (Pp.braces (Pp.list pp_int_pair pos))));
       fail {loc; msg = Parser (Cparser_unexpected_token (where ^ "\n" ^ message))}
  in
  return parsed_spec


let parse_function_spec (Attrs attributes) =
  let attributes = List.rev attributes in
  let@ conditions =
    ListM.concat_mapM (fun attr ->
        let k = (Option.value ~default:"<>" (Option.map Id.s attr.attr_ns), Id.s attr.attr_id) in
        (* FIXME (TS): I'm not sure if the check against cerb::magic was strange,
            or if it was checking the wrong thing the whole time *)
        let use = List.exists (fun (x, y) -> String.equal x (fst k) && String.equal y (snd k))
            [("cerb", "magic"); ("cn", "requires"); ("cn", "ensures");
                ("cn", "accesses"); ("cn", "trusted")] in
        if use then 
          ListM.concat_mapM (fun (loc, arg, _) ->
              parse C_parser.function_spec (loc, arg)
            ) attr.attr_args
        else return []
      ) attributes
  in
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

let parse_inv_spec (Attrs attributes) =
  ListM.concat_mapM (fun attr ->
      match Option.map Id.s (attr.attr_ns), Id.s (attr.attr_id) with
      | Some "cerb", "magic" ->
         ListM.concat_mapM (fun (loc, arg, _) ->
             let@ (Cn.CN_inv (_loc, conds)) = parse C_parser.loop_spec (loc, arg) in
             return conds
           ) attr.attr_args
      | _ ->
         return []
    ) attributes


