{

}

rule main = parse
  (* skip spaces *)
  | [' ' '\t']+
      { main lexbuf }
  
  (* integer constants *)
  | ('-'?)['0'-'9']+ as integer
      { CONST (int_of_string integer) }
  
  (* symbolic names *)
  | ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as s
      { SYM s }
  
  (* symbolic names *)
  | ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as f
      { FNAME f }
  
  | "skip" { SKIP }
  
  | "not" { NOT }
  
  | "true" { TRUE }
  | "false" { FALSE }
  
  | "let" { LET }
  | "in" { IN }
  
  | "fun" { FUN }
  | "end" { END }
  
  (* binary operators *)
  | '+'   { PLUS }
  | '-'   { MINUS }
  | '*'   { STAR }
  | '/'   { SLASH }
  | '%'   { PERCENT }
  | '='   { EQ }
  | '<'   { LT }
  | "/\\" { SLASH_BACKSLASH }
  | "\/"  { BACKSLASH_SLASH }
  
  (* negative action *)
  | '~' { TILDE }
  
  (* negative marker *)
  | '!' { EXCLAM }
  
  (* sequencing operators *)
  | "||"  { PIPE_PIPE }
  | ';'   { SEMICOLON }
  | "|>"  { PIPE_GT }
  | ">>"  { GT_GT }
  
  (* pattern symbols *)
  | "()" { LPAREN_RPAREN }
  | "_"  { UNDERSCORE }
  
  | "<- " { LT_MINUS }
  | '('   { LPAREN }
  | ')'   { RPAREN }
  | '{'   { LBRACE }
  | '}'   { RBRACE }
  | '['	  { LBRACKET }
  | ']'	  { RBRACKET }
  | ','   { COMMA }
  | ':'   { COLON }
  | ":="   { COLON_EQ }
  
  | "create" { CREATE }
  | "alloc" { ALLOC }
  | "kill" { KILL }
  | "store" { STORe }
  | "load" { LOAD }

  | "same" { SAME }

  | "undef" { UNDEF }
  | "error" { ERROR }

  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  
  (* TODO: hack *)
  | "signed" { SIGNED }
  | "int" { INT }
