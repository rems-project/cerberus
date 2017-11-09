open Parser
open Tokens

let string_of_pos pos =
  Lexing.(Printf.sprintf "<%s:%d:%d>" pos.pos_fname pos.pos_lnum
                        (1 + pos.pos_cnum - pos.pos_bol))

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


module StringConcatenation = struct
  (* TODO: the location of the token following a string literal is broken (shows the start of the string) *)
  let state = ref None
  
  let lexer lexbuf =
    let rec concatStrings (previous_pref_opt, strs_acc) =
(* (TODO: location broken)
      let saved_lex_curr_p = lexbuf.Lexing.lex_curr_p in
*)
      match Lexer.lexer lexbuf with
        | STRING_LITERAL (new_pref_opt, strs) ->
            begin match merge_encoding_prefixes previous_pref_opt new_pref_opt with
              | Some pref_opt ->
                  concatStrings (pref_opt, strs_acc @ strs)
              | None ->
                  raise NonStandard_string_concatenation
            end
        | tok ->
(* (TODO: location broken)           lexbuf.Lexing.lex_curr_p <- saved_lex_curr_p; *)
            (STRING_LITERAL (previous_pref_opt, strs_acc), tok)
    in
    
    match !state with
      | Some tok ->
          state := None;
          tok
      | None ->
          begin match Lexer.lexer lexbuf with
            | STRING_LITERAL lit ->
                let saved_lex_start_p = lexbuf.Lexing.lex_start_p in
                let (str_tok, tok') = concatStrings lit in
                state := Some tok';
                lexbuf.Lexing.lex_start_p <- saved_lex_start_p;
                str_tok
            | tok ->
                (* TODO(victor): fix position error *)
                (*print_endline (Tokens.string_of_token tok ^ string_of_loc (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf));*)
                tok
          end
end


let parse input =
  let parse_channel ic =
    let lexbuf = Lexer.init ic in
    let fail lexbuf =
      let cause = Errors.Cparser_cause
          (Errors.Cparser_unexpectedToken (Lexing.lexeme lexbuf))
      in
      let loc = Lexing.lexeme_start_p lexbuf |> Location_ocaml.point in
      Exception.fail (loc, cause)
    in
    
    try
      Parser.translation_unit StringConcatenation.lexer lexbuf
      |> Exception.except_return
    with
    | Failure msg ->
        prerr_endline "DEBUG: CPARSER_DRIVER, Failure";
        failwith msg
    | NonStandard_string_concatenation ->
        prerr_endline "ERROR: unsupported non-standard concatenation of string literals";
        fail lexbuf
    | _ ->
      fail lexbuf
  in
  Input.read parse_channel input
