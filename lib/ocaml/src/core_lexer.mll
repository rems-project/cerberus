{
module P = Core_parser
}

rule main = parse
  (* skip spaces *)
  | [' ' '\t']+
      { main lexbuf }
  
  (* integer constants *)
  | ('-'?)['0'-'9']+ as integer
      { P.CONST (int_of_string integer) }
  
  (* symbolic names *)
  | ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as s
      { P.SYM s }
  
  (* symbolic names *)
  | ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as f
      { P.FNAME f }
  
  | "skip" { P.SKIP }
  
  | "not" { P.NOT }
  
  | "true" { P.TRUE }
  | "false" { P.FALSE }
  
  | "let" { P.LET }
  | "in" { P.IN }
  
  | "fun" { P.FUN }
  | "end" { P.END }
  
  (* binary operators *)
  | '+'   { P.PLUS }
  | '-'   { P.MINUS }
  | '*'   { P.STAR }
  | '/'   { P.SLASH }
  | '%'   { P.PERCENT }
  | '='   { P.EQ }
  | '<'   { P.LT }
  | "/\\" { P.SLASH_BACKSLASH }
  | "\\/"  { P.BACKSLASH_SLASH }
  
  (* negative action *)
  | '~' { P.TILDE }
  
  (* negative marker *)
  | '!' { P.EXCLAM }
  
  (* sequencing operators *)
  | "||"  { P.PIPE_PIPE }
  | ';'   { P.SEMICOLON }
  | "|>"  { P.PIPE_GT }
  | ">>"  { P.GT_GT }
  
  (* pattern symbols *)
  | "()" { P.LPAREN_RPAREN }
  | "_"  { P.UNDERSCORE }
  
  | "<- " { P.LT_MINUS }
  | '('   { P.LPAREN }
  | ')'   { P.RPAREN }
  | '{'   { P.LBRACE }
  | '}'   { P.RBRACE }
  | '['	  { P.LBRACKET }
  | ']'	  { P.RBRACKET }
  | ','   { P.COMMA }
  | ':'   { P.COLON }
  | ":="   { P.COLON_EQ }
  
  | "create" { P.CREATE }
  | "alloc" { P.ALLOC }
  | "kill" { P.KILL }
  | "store" { P.STORE }
  | "load" { P.LOAD }

  | "same" { P.SAME }

  | "undef" { P.UNDEF }
  | "error" { P.ERROR }

  | "if" { P.IF }
  | "then" { P.THEN }
  | "else" { P.ELSE }
  
  (* TODO: hack *)
  | "signed" { P.SIGNED }
  | "int" { P.INT }
