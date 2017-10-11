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

let parse input =
  let parse_channel ic =
    let lexbuf = Lexer.init (Input.name input) ic in
    let fail lexbuf =
      let cause = Errors.Cparser_cause
          (Errors.Cparser_unexpectedToken (Lexing.lexeme lexbuf))
      in
      let loc = Lexing.lexeme_start_p lexbuf |> Location_ocaml.point in
      Exception.fail (loc, cause)
    in
    try
      Parser.translation_unit Lexer.lexer lexbuf
      |> Exception.except_return
    with
    | Failure msg ->
      prerr_endline "DEBUG: CPARSER_DRIVER, Failure";
      failwith msg
    | NonStandard_string_concatenation ->
      prerr_endline "ERROR: unsupported non-standard concatenation \
                     of string literals";
      fail lexbuf
    | _ ->
      fail lexbuf
  in
  Input.read parse_channel input
