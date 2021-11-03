(* adapting from core_lexer *)
{
  exception Error

  module T = Assertion_parser_util
}

rule main = parse
  (* skip spaces *)
  | [' ' '\t']+ { main lexbuf }
  
  | "true"   { T.TRUE }
  | "false"  { T.FALSE }

  (* integer constants *)
  | ['0'-'9']+ as z  { T.Z (Z.of_string z) }

  | "let" { T.LET }
  | "="   { T.EQUAL }
  | "unchanged" { T.UNCHANGED }
  

  (* binary operators *)
  | '+'   { T.PLUS }
  | '-'   { T.MINUS }
  | '*'   { T.STAR }
  | '/'   { T.SLASH }
  | "power"   { T.POWER }
  | "%"   { T.PERCENT }

  | "=="  { T.EQ }
  | "!="  { T.NE }
  | '<'   { T.LT }
  | '>'   { T.GT }
  | "<="  { T.LE }
  | ">="  { T.GE }

  | "flipBit" { T.FLIPBIT }

  | "(pointer)"   { T.POINTERCAST }
  | "(integer)"   { T.INTEGERCAST }

  | "pointer"     { T.POINTER }
  | "integer"     { T.INTEGER }

  | '('   { T.LPAREN }
  | ')'   { T.RPAREN }
  | '['   { T.LBRACKET }
  | ']'   { T.RBRACKET }
  | '{'   { T.LBRACE }
  | '}'   { T.RBRACE }
  | ','   { T.COMMA }
  | ';'   { T.SEMICOLON }

  | '?'   { T.QUESTION }
  | ':'   { T.COLON }
  | "||"  { T.OR }
  | "&&"  { T.AND }

  | "NULL" { T.NULL }
  | "offsetof" { T.OFFSETOF }

  | '&'   { T.AMPERSAND }
  | '@'   { T.AT }

  | "each" {T.EACH }
  
  | '\n' {Lexing.new_line lexbuf; main lexbuf}

  (* names *)
  | ['_' 'a'-'z' 'A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as name
      { T.NAME name }
  | '.' (['_' 'a'-'z' 'A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as member)
      { T.MEMBER member }
  | ".."
      { T.DOTDOT }


  | eof  { T.EOF }
  | _
    { raise Error }
