open Parser


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
