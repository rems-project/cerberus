open Parser


(*
type input = in_channel
val read : (input -> 'a) -> t -> 'a
*)




let parse input : Cabs0.definition list =
  (* TODO: hack *)
  Lexer.contexts := [];
  Input.read (fun ic ->
    let lexbuf = Lexer.init (Input.name input) ic in
    let lexbuf2 = {lexbuf with Lexing.refill_buff = lexbuf.Lexing.refill_buff} in (* Black magic *)
    try
      Pre_parser.translation_unit_file Lexer.initial lexbuf;
      Pervasives.seek_in ic 0;
      
      Parser.translation_unit_file Lexer.hack lexbuf2
    with
      | _ ->
          let tok = Lexing.lexeme lexbuf in
          let spos = Lexing.lexeme_start_p lexbuf in
          Printf.printf "PARSING ERROR: unexpected token: `%s' @ line: %d, char: %d\n"
            tok spos.Lexing.pos_lnum (spos.Lexing.pos_cnum - spos.Lexing.pos_bol);
          exit 1
  ) input

(*
let parse input : Cabs0.definition list =
  (* TODO: hack *)
  Lexer.contexts := [];
  Input.read (fun ic ->
    let rec inf = Datatypes.S inf in
    Obj.magic
      (match Parser.parse inf (Lexer.tokens_stream (Lexer.init (Input.name input) ic)) with
        | Parser.Inter.Fail_pr            -> failwith "Internal error while parsing"
        | Parser.Inter.Timeout_pr         -> assert false
        | Parser.Inter.Parsed_pr (ast, _) -> ast)
  ) input
*)
