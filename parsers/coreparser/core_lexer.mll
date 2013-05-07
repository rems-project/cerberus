{
open Pervasives_

module P = Core_parser
type token = P.token

let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Pervasives.compare)
    [
      (* ctype tokens *)
      ("const",    P.CONST);
      ("restrict", P.RESTRICT);
      ("volatile", P.VOLATILE);
      ("_Atomic",  P.ATOMIC);
      ("short",    P.SHORT);
      ("int",      P.INT);
      ("long",     P.LONG);
      ("bool",     P.BOOL);
      ("signed",   P.SIGNED);
      ("unsigned", P.UNSIGNED);
      ("float",    P.FLOAT);
      ("double",   P.DOUBLE);
      ("_Complex", P.COMPLEX);
      ("char",     P.CHAR);
      ("void",     P.VOID);
      ("struct",   P.STRUCT);
      ("union",    P.UNION);
      ("enum",     P.ENUM);
      ("size_t",   P.SIZE_T);
      ("intptr_t", P.INTPTR_T);
      ("wchar_t",  P.WCHAR_T);
      ("char16_t", P.CHAR16_T);
      ("char32_t", P.CHAR32_T);
      ("enum",     P.ENUM);
      
      ("integer", P.INTEGER);
      ("boolean", P.BOOLEAN);
      ("address", P.ADDRESS);
      ("ctype",   P.CTYPE  );
      ("unit",   P.UNIT    );
      ("skip",   P.SKIP    );
      ("not",    P.NOT     );
      ("true",   P.TRUE    );
      ("false",  P.FALSE   );
      ("let",    P.LET     );
      ("in",     P.IN      );
      ("fun",    P.FUN     );
      ("proc",    P.FUN     );
      ("end",    P.END     );
      ("create", P.CREATE  );
      ("alloc",  P.ALLOC   );
      ("kill",   P.KILL    );
      ("store",  P.STORE   );
      ("load",   P.LOAD    );
      ("same",   P.SAME    );
      ("undef",  P.UNDEF   );
      ("error",  P.ERROR   );
      ("if",     P.IF      );
      ("then",   P.THEN    );
      ("else",   P.ELSE    );
      ("ret",    P.RET     );
      ("save",   P.SAVE    );
      ("run",    P.RUN     );
    ]

let scan_sym lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    Pmap.find id keywords
  (* default to variable name, as opposed to type *)
  with Not_found ->
    (* Check if the token is an enumeration constant *)
      P.SYM id


let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf

}


let symbolic_name = ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']*


rule main = parse
  (* beginning of a comment *)
  | "{-"
      { let _ = comment lexbuf in main lexbuf }
  
  (* single-line comment *)
  | "--"
      { let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; main lexbuf }
  
  (* skip spaces *)
  | [' ' '\t']+
      { main lexbuf }
  
  (* integer constants *)
  | ('-'?)['0'-'9']+ as integer
      { P.INT_CONST (int_of_string integer) }
  
  (* binary operators *)
  | '+'   { P.PLUS }
  | '-'   { P.MINUS }
  | '*'   { P.STAR }
  | '/'   { P.SLASH }
  | '%'   { P.PERCENT }
  | '='   { P.EQ }
  | '<'   { P.LT }
  | "/\\" { P.SLASH_BACKSLASH }
  | "\\/" { P.BACKSLASH_SLASH }
  
  (* negative action *)
  | '~' { P.TILDE }
  
  (* negative marker *)
  | '!' { P.EXCLAM }
  
  (* sequencing operators *)
  | "||"  { P.PIPE_PIPE }
  | ';'   { P.SEMICOLON }
  | ">>"  { P.GT_GT }
  | "|>"  { P.PIPE_GT }
  
  (* pattern symbols *)
  | "_"  { P.UNDERSCORE }
  
  | "<- " { P.LT_MINUS }
  | '('   { P.LPAREN }
  | ')'   { P.RPAREN }
  | '{'   { P.LBRACE }
  | '}'   { P.RBRACE }
  | '['	  { P.LBRACKET }
  | ']'	  { P.RBRACKET }
  | '.'   { P.DOT }
  | ','   { P.COMMA }
  | ':'   { P.COLON }
  | ":="  { P.COLON_EQ }

  | symbolic_name { scan_sym lexbuf }
  | '\n' {Lexing.new_line lexbuf; main lexbuf}
  | eof  {P.EOF}
  | _
    { raise_error ("Unexpected symbol \""
                   ^ Lexing.lexeme lexbuf ^ "\" in "
                   ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
                   ^ ".\n")
    }


and comment = parse
  | "-}"
      { [] }
  | _
      {lex_comment comment lexbuf}


and onelinecomment = parse
  | '\n' | eof
      { [] }
  | _
      { lex_comment onelinecomment lexbuf }
