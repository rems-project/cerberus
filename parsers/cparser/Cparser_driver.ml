open Parser
open Tokens
open Pre_parser_aux

(*
type input = in_channel
val read : (input -> 'a) -> t -> 'a
*)


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


let parse input : Cabs.translation_unit =
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
      saved_tokens := tok :: !saved_tokens;
      tok in
    
    let hack lexbuf =
      match !saved_tokens with
        | [] ->
            EOF
        | tk :: tks ->
            saved_tokens := tks;
            tk in
    
    let modify_tokens () =
      let modify = function
        | TYPEDEF_NAME (id, typ)
        | UNKNOWN_NAME (id, typ)
        | VAR_NAME     (id, typ) ->
            begin
              match !typ with
                | VarId       -> VAR_NAME2 id
                | TypedefId   -> TYPEDEF_NAME2 id
                | OtherId str -> OTHER_NAME id
            end
        | tok -> tok in
      
      let (_, tks') =
        List.fold_left (fun (str_acc, acc) tk ->
          match (str_acc, tk) with
(*
            | (Some (str, loc), STRING_LITERAL (str', loc')) -> (Some (str' ^ str, loc'), acc)
            | (None           , STRING_LITERAL (str, loc)  ) -> (Some (str, loc), acc)
            | (Some (str, loc), _                          ) -> (None, modify tk :: CONSTANT (Cabs0.CONST_STRING str, loc) :: acc)
            | (None           , _                          ) -> (None, modify tk :: acc)
*)
            (* STD §6.4.5#5 *)
            (* TODO: this is partial + we only allow the concatenation of identically prefixed literals,
                     but it is impl-def whether more concatenations are allowed ... *)
            | (Some (pref1_opt, str1), STRING_LITERAL (pref2_opt, str2)) ->
                (* we don't support non-standard concatenation for now (neither gcc nor clang seems to do either) *)
                (match merge_encoding_prefixes pref1_opt pref2_opt with
                  | Some pref_opt -> (Some (pref_opt, str2 @ str1), acc)
                  | None          -> raise NonStandard_string_concatenation)
            | (None, STRING_LITERAL lit) ->
                (Some lit, acc)
            | (Some lit, _) ->
                (None, modify tk :: STRING_LITERAL lit :: acc)
            | (None, _) ->
                (None, modify tk :: acc)
        ) (None, []) !saved_tokens in
      saved_tokens := tks' in
    
    try
(*
      print_endline "RUNNING pre_parser";
*)
      Pre_parser.translation_unit_file lexer_wrapper lexbuf;
(*
      print_endline "DONE";
      
      print_endline "=== TOKENS before ===";
      List.iter (fun tk -> print_endline (string_of_token tk)) (List.rev !saved_tokens);
*)
      
      
      modify_tokens ();
      
      
(*
      print_newline ();
      print_endline "=== TOKENS after ===";
      List.iter (fun tk -> print_endline (string_of_token tk)) !saved_tokens;
*)
      
      
      Parser.translation_unit_file hack (Lexing.from_string "")
    with
      | Failure msg -> raise (Failure msg)
      | err ->
          let tok  = Lexing.lexeme lexbuf in
          let spos = Lexing.lexeme_start_p lexbuf in
          (match err with
            | NonStandard_string_concatenation ->
                print_endline "ERROR: unsupported non-standard concatenation of string literals"
            | _ -> ());
          Printf.printf "PARSING ERROR: unexpected token: `%s' @ line: %d, char: %d\n"
            tok spos.Lexing.pos_lnum (spos.Lexing.pos_cnum - spos.Lexing.pos_bol);
          exit 1
  ) input
