(* open Cerb_frontend *)
open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Pp
module Cn = Cerb_frontend.Cn


module Loc = Locations

(* adapting from core_parser_driver.ml *)

let parse parser_start (loc, string) = 
  let lexbuf = Lexing.from_string string in
  let () = 
    let open Location_ocaml in
    Lexing.set_position lexbuf
      (* revisit *)
      begin match Location_ocaml.to_raw loc with
      | Loc_unknown -> lexbuf.lex_curr_p
      | Loc_other _ -> lexbuf.lex_curr_p
      | Loc_point pos -> pos
      (* start, end, cursor *)
      | Loc_region (pos, _, _ ) -> pos
      | Loc_regions ([],_) -> lexbuf.lex_curr_p 
      | Loc_regions ((pos,_) :: _, _) -> pos
      end
  in
  let () = match Location_ocaml.get_filename loc with
    | Some filename -> lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname= filename }
    | None -> () 
  in
  let@ parsed_spec =
    try return (parser_start C_lexer.lexer lexbuf) with
    | C_lexer.Error err ->
       let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
       fail {loc; msg = Parser err}
    | C_parser.Error ->
       let loc = Location_ocaml.(region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) NoCursor) in
       fail {loc; msg = Generic !^ ("Unexpected token " ^ Lexing.lexeme lexbuf)}
  in
  return parsed_spec


let parse_function_spec (Attrs attributes) =
  let attributes = List.rev attributes in
  let@ conditions =
    ListM.concat_mapM (fun attr ->
        match Option.map Id.s (attr.attr_ns), Id.s (attr.attr_id) with
        | Some "cerb", "magic" ->
           ListM.mapM (fun (loc, arg, _) ->
               parse C_parser.function_spec (loc, arg)
             ) attr.attr_args
        | _ ->
           return []
      ) attributes
  in
  ListM.fold_leftM (fun acc cond ->
    match cond, acc with
    | (Cn.CN_trusted loc), (_, [], [], []) ->
       return (Mucore.Trusted loc, [], [], [])
    | (Cn.CN_trusted loc), _ ->
       fail {loc; msg= Generic !^"Please specify 'trusted' before other conditions"}
    | (CN_accesses (loc, ids)), (trusted, accs, [], []) ->
       return (trusted, accs @ List.map (fun id -> (loc, id)) ids, [], [])
    | (CN_accesses (loc, _)), _ ->
       fail { loc; msg= Generic !^"Please specify 'accesses' before any 'requires' and 'ensures'" }
    | (CN_requires (loc, cond)), (trusted, accs, reqs, []) ->
       return (trusted, accs, reqs @ [(loc, cond)], [])
    | (CN_requires (loc, _)), _ ->
       fail {loc; msg = Generic !^"Please specify 'requires' before any 'ensures'"}
    | (CN_ensures (loc, cond)), (trusted, accs, reqs, enss) ->
       return (trusted, accs, reqs, enss @ [(loc, cond)])
    )
    (Mucore.Checked, [], [], []) conditions

let parse_inv_spec (Attrs attributes) =
  let@ conditions =
    ListM.concat_mapM (fun attr ->
        match Option.map Id.s (attr.attr_ns), Id.s (attr.attr_id) with
        | Some "cerb", "magic" ->
           ListM.mapM (fun (loc, arg, _) ->
               parse C_parser.loop_spec (loc, arg)
             ) attr.attr_args
        | _ ->
           return []
      ) attributes
  in
  return (List.map (fun (Cn.CN_inv (_loc, cond)) -> cond) conditions)
