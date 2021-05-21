(* adapting from core_lexer *)
{
  exception Error

  module T = Assertion_parser_util
}

rule main = parse
  (* skip spaces *)
  | [' ' '\t']+ { main lexbuf }
  
  (* integer constants *)
  | ['0'-'9']+ as z  { T.Z (Z.of_string z) }
  
  (* binary operators *)
  | '+'   { T.PLUS }
  | '-'   { T.MINUS }
  | '*'   { T.STAR }
  | '/'   { T.SLASH }
  | "power"   { T.POWER }

  | "=="  { T.EQ }
  | "!="  { T.NE }
  | '<'   { T.LT }
  | '>'   { T.GT }
  | "<="  { T.LE }
  | ">="  { T.GE }

  | "(pointer)"   { T.POINTERCAST }
  
  | '('   { T.LPAREN }
  | ')'   { T.RPAREN }
  | ','   { T.COMMA }

  | '?'   { T.QUESTION }
  | ':'   { T.COLON }

  | '&'   { T.AMPERSAND }
  | '@'   { T.AT }
  
  | '\n' {Lexing.new_line lexbuf; main lexbuf}


(*  | "Owned" { T.OWNED } *)
(*  | "Block" { T.BLOCK } *)

  (* names *)
  | ['_' 'a'-'z' 'A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as name
      { T.NAME name }
  | '.' (['_' 'a'-'z' 'A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as member)
      { T.MEMBER member }


  | eof  { T.EOF }
  | _
    { raise Error }
