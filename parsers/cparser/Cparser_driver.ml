open Parser
open Tokens
open Pre_parser_aux


let string_of_pos pos =
  Lexing.(
    Printf.sprintf "<%s:%d:%d>" pos.pos_fname pos.pos_lnum (1 + pos.pos_cnum - pos.pos_bol)
  )

let string_of_loc (start_p, end_p) = 
  string_of_pos start_p ^ " - " ^ string_of_pos end_p




(* TODO: get rid of that *)
exception NonStandard_string_concatenation


let merge_encoding_prefixes pref1_opt pref2_opt =
  match (pref1_opt, pref2_opt) with
    | (None, None) ->
        Some None
    | (None     , Some pref)
    | (Some pref, None     ) ->
        Some (Some pref)
    | (Some pref1, Some pref2) when pref1 = pref2 ->
        Some (Some pref1)
    | _ ->
        None


module M = Map.Make (struct
  type t = string
  let compare = Pervasives.compare
end)

let seen_typedefs : (identifier_type M.t) ref =
  ref M.empty


let parse input =
  (* TODO: hack *)
  Lexer.contexts := [];
  Input.read (fun ic ->
    let lexbuf  = Lexer.init (Input.name input) ic in
    
    (* Here will be saved the tokens seen while running the pre_parser (+ the
       modification made for names) *)
    let saved_tokens = ref [] in
    
    (* This wrapper is feed to the pre_parser and incrementaly save the list of tokens *)
    let lexer_wrapper lexbuf =
      let tok = Lexer.initial lexbuf in
(*      print_endline ("TOKEN => " ^ Tokens.string_of_token tok); *)
      saved_tokens := (tok, (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)) :: !saved_tokens;
      tok in
    
    let hack lexbuf =
      match !saved_tokens with
        | (tok, (start_p, end_p)) :: xs ->
(*            Printf.printf "TOKEN => %s @ line: %d, char: %d -- line: %d, char: %d\n" (Tokens.string_of_token tok)
              start_p.Lexing.pos_lnum (start_p.Lexing.pos_cnum - start_p.Lexing.pos_bol)
              end_p.Lexing.pos_lnum (end_p.Lexing.pos_cnum - end_p.Lexing.pos_bol);
            flush_all (); *)
            saved_tokens := xs;
            lexbuf.Lexing.lex_start_p <- start_p;
            lexbuf.Lexing.lex_curr_p <- end_p;
            tok
        | [] ->
            prerr_endline "ERROR (Cparser_driver.hack ==> []"; exit 1 in
    
    let modify_tokens () =
      let modify = function
        | TYPEDEF_NAME (id, typ)
        | UNKNOWN_NAME (id, typ)
        | VAR_NAME     (id, typ) ->
(*
            if M.mem id !seen_typedefs then
              Printf.printf "====> ALREADY SEEN: %s with typ: %s (now has typ: %s)\n"
                id (string_of_typ (M.find id !seen_typedefs)) (string_of_typ !typ)
            else
              seen_typedefs := M.add id !typ !seen_typedefs;
*)
            begin
              match !typ with
                | VarId       -> VAR_NAME2 id
                | TypedefId   -> TYPEDEF_NAME2 id
                | OtherId str -> OTHER_NAME id
            end
        | tok -> tok in
      
      let (_, xs') =
        List.fold_left (fun (str_acc, acc) (tok, loc) ->
          match (str_acc, tok) with
(*
            | (Some (str, loc), STRING_LITERAL (str', loc')) -> (Some (str' ^ str, loc'), acc)
            | (None           , STRING_LITERAL (str, loc)  ) -> (Some (str, loc), acc)
            | (Some (str, loc), _                          ) -> (None, modify tk :: CONSTANT (Cabs0.CONST_STRING str, loc) :: acc)
            | (None           , _                          ) -> (None, modify tk :: acc)
*)
            (* STD §6.4.5#5 *)
            (* TODO: this is partial + we only allow the concatenation of identically prefixed literals,
                     but it is impl-def whether more concatenations are allowed ... *)
            | (Some ((pref1_opt, str1), lit_loc), STRING_LITERAL (pref2_opt, str2)) ->
                (* we don't support non-standard concatenation for now (neither gcc nor clang seems to do either) *)
                (match merge_encoding_prefixes pref1_opt pref2_opt with
                  | Some pref_opt -> (Some ((pref_opt, str2 @ str1), lit_loc), acc)
                  | None          -> raise NonStandard_string_concatenation)
            | (None, STRING_LITERAL lit) ->
                (Some (lit, loc), acc)
            | (Some (lit, lit_loc), _) ->
                (None, (modify tok, loc) :: (STRING_LITERAL lit, lit_loc) :: acc)
            | (None, _) ->
                (None, (modify tok, loc) :: acc)
        ) (None, []) !saved_tokens in
      saved_tokens := xs' in
    
    try
      
(*      print_endline "BEFORE PRE PARSER"; *)
      Pre_parser.translation_unit_file lexer_wrapper lexbuf;
(*      print_endline "AFTER PRE PARSER"; *)
(*
      print_endline "==== BEFORE LEXER HACK ====";
      List.iter (fun (tok, loc) ->
        Printf.printf "%s\t\tLoc=%s\n" (string_of_token tok) (string_of_loc loc)
      ) (List.rev !saved_tokens);
      print_endline "===========================";
*)

      modify_tokens ();
(* *)
      Debug_ocaml.print_debug 8 [Debug_ocaml.DB_cparser] "==== AFTER LEXER HACK ====";
      List.iter (fun (tok, loc) ->
        Debug_ocaml.print_debug 8 [Debug_ocaml.DB_cparser]
          (Printf.sprintf "%s\t\tLoc=%s\n" (string_of_token tok) (string_of_loc loc))
      ) !saved_tokens;
      Debug_ocaml.print_debug 8 [Debug_ocaml.DB_cparser] "===========================";
(* *)
      Exception.except_return (Parser.translation_unit_file hack (Lexing.from_string ""))
    with
      | Failure msg ->
          prerr_endline "DEBUG: CPARSER_DRIVER, Failure";
          raise (Failure msg)
      
      | PreParser_undeclared_identifier (str, loc) ->
          prerr_endline "DEBUG: CPARSER_DRIVER, PreParser_undeclared_identifier";
          Exception.fail (loc, Errors.(Cparser_cause (Cparser_undeclaredIdentifier str)))
      
      | err ->
          let tok  = Lexing.lexeme lexbuf in
          let spos = Lexing.lexeme_start_p lexbuf in
          (match err with
            | NonStandard_string_concatenation ->
                prerr_endline "ERROR: unsupported non-standard concatenation of string literals"
            | _ -> ());
          Exception.fail (Location_ocaml.point spos, Errors.(Cparser_cause (Cparser_unexpectedToken tok)))
(*
          Printf.printf "PARSING ERROR: unexpected token: `%s' @ line: %d, char: %d\n"
            tok spos.Lexing.pos_lnum (spos.Lexing.pos_cnum - spos.Lexing.pos_bol);
          exit 1
*)
  ) input
