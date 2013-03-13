open Parser

let parse file : Cabs0.definition list =
  let ic = open_in file in
  let lb = Lexer.init file ic in
  let rec inf = Datatypes.S inf in
  Obj.magic
    (match Parser.parse inf (Lexer.tokens_stream lb) with
      | Parser.Inter.Fail_pr            -> failwith "Internal error while parsing"
      | Parser.Inter.Timeout_pr         -> assert false
      | Parser.Inter.Parsed_pr (ast, _) -> ast)
