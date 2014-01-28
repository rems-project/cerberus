open Parser
open Tokens
open Pre_parser_aux

(*
type input = in_channel
val read : (input -> 'a) -> t -> 'a
*)




let parse input : Cabs0.definition list =
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
        | TYPEDEF_NAME (id, typ, loc)
        | UNKNOWN_NAME (id, typ, loc)
        | VAR_NAME     (id, typ, loc) ->
            begin
              match !typ with
                | VarId       -> VAR_NAME2 (id, loc)
                | TypedefId   -> TYPEDEF_NAME2 (id, loc)
                | OtherId str -> OTHER_NAME (id, loc)
            end
        | tok -> tok in
      
      let (_, tks') =
        List.fold_left (fun (str_acc, acc) tk ->
          match (str_acc, tk) with
            | (Some (str, loc), STRING_LITERAL (str', loc')) -> (Some (str' ^ str, loc'), acc)
            | (None           , STRING_LITERAL (str, loc)  ) -> (Some (str, loc), acc)
            | (Some (str, loc), _                          ) -> (None, modify tk :: CONSTANT_ (Cabs0.CONST_STRING str, loc) :: acc)
            | (None           , _                          ) -> (None, modify tk :: acc)
        ) (None, []) !saved_tokens in
      saved_tokens := tks' in
    
    try
      Pre_parser.translation_unit_file lexer_wrapper lexbuf;
      modify_tokens ();
      
      Parser.translation_unit_file hack (Lexing.from_string "")
    with
      | _ ->
          let tok = Lexing.lexeme lexbuf in
          let spos = Lexing.lexeme_start_p lexbuf in
          Printf.printf "PARSING ERROR: unexpected token: `%s' @ line: %d, char: %d\n"
            tok spos.Lexing.pos_lnum (spos.Lexing.pos_cnum - spos.Lexing.pos_bol);
          exit 1
  ) input
