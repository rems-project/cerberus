{
open Pervasives_

module P = Core_parser



let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Pervasives.compare)
    [
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
      (* TODO: hack *)
      ("signed", P.SIGNED  );
      ("int",    P.INT     );
    ]

let scan_sym lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    Pmap.find id keywords
  (* default to variable name, as opposed to type *)
  with Not_found ->
    (* Check if the token is an enumeration constant *)
      P.SYM id

}


let symbolic_name = ['a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']*


rule main = parse
  (* skip spaces *)
  | [' ' '\t']+
      { main lexbuf }
  
  (* integer constants *)
  | ('-'?)['0'-'9']+ as integer
      { P.CONST (int_of_string integer) }
  
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
  | ">>"  { P.GT_GT }
  | "|>"  { P.PIPE_GT }
  
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
  
  | symbolic_name { scan_sym lexbuf }
  | '\n' {Lexing.new_line lexbuf; main lexbuf}
  | eof  {P.EOF}
  | _
    { raise_error ("Unexpected symbol \""
                   ^ Lexing.lexeme lexbuf ^ "\" in "
                   ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
                   ^ ".\n")
    }
