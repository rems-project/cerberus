{
open Pervasives_

module T = Core_parser_util
type token = T.token

let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Pervasives.compare)
    [
      (* ctype tokens *)
      ("_Atomic",     T.ATOMIC);
      ("short",       T.SHORT);
      ("int",         T.INT);
      ("long",        T.LONG);
      ("long_long",   T.LONG_LONG);
      ("bool",        T.BOOL);
      ("signed",      T.SIGNED);
      ("unsigned",    T.UNSIGNED);
      ("float",       T.FLOAT);
      ("double",      T.DOUBLE);
      ("long_double", T.LONG_DOUBLE);
      ("_Complex",    T.COMPLEX);
      ("char",        T.CHAR);
      ("ichar",       T.ICHAR);
      ("void",        T.VOID);
      ("struct",      T.STRUCT);
      ("union",       T.UNION);
      ("enum",        T.ENUM);
      ("size_t",      T.SIZE_T);
      ("intptr_t",    T.INTPTR_T);
      ("wchar_t",     T.WCHAR_T);
      ("char16_t",    T.CHAR16_T);
      ("char32_t",    T.CHAR32_T);
      
      ("def",     T.DEF     ); (* for implementation files only *)
      ("integer", T.INTEGER );
      ("boolean", T.BOOLEAN );
      ("address", T.ADDRESS );
      ("ctype",   T.CTYPE   );
      ("unit",    T.UNIT    );
      ("skip",    T.SKIP    );
      ("not",     T.NOT     );
      ("true",    T.TRUE    );
      ("false",   T.FALSE   );
      ("let",     T.LET     );
      ("in",      T.IN      );
      ("fun",     T.FUN     );
      ("proc",    T.FUN     );
      ("end",     T.END     );
      ("create",  T.CREATE  );
      ("alloc",   T.ALLOC   );
      ("kill",    T.KILL    );
      ("store",   T.STORE   );
      ("load",    T.LOAD    );
      ("same",    T.SAME    );
      ("undef",   T.UNDEF   );
      ("error",   T.ERROR   );
      ("if",      T.IF      );
      ("then",    T.THEN    );
      ("else",    T.ELSE    );
      ("ret",     T.RET     );
      ("save",    T.SAVE    );
      ("run",     T.RUN     );
      ("case",    T.CASE    );
      ("of",      T.OF      );
      ("seq_cst", T.SEQ_CST );
      ("relaxed", T.RELAXED );
      ("release", T.RELEASE );
      ("acquire", T.ACQUIRE );
      ("consume", T.CONSUME );
      ("acq_rel", T.ACQ_REL );

(* TODO: temporary *)
      ("is_scalar",   T.IS_SCALAR  );
      ("is_integer",  T.IS_INTEGER );
      ("is_signed",   T.IS_SIGNED  );
      ("is_unsigned", T.IS_UNSIGNED);
    ]

let scan_sym lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    Pmap.find id keywords
  with Not_found ->
    T.SYM id

let scan_impl lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    T.IMPL (Pmap.find id Implementation.impl_map)
  with Not_found ->
    failwith "Found an invalid impl_name."

let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf

}


let impl_name = '<' ['A'-'Z' 'a'-'z' '_']* '>'
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
      { T.INT_CONST (Num.num_of_string integer) }
  
  (* binary operators *)
  | '+'   { T.PLUS }
  | '-'   { T.MINUS }
  | '*'   { T.STAR }
  | '/'   { T.SLASH }
  | '%'   { T.PERCENT }
  | '='   { T.EQ }
  | '<'   { T.LT }
  | "<="  { T.LE }
  | "/\\" { T.SLASH_BACKSLASH }
  | "\\/" { T.BACKSLASH_SLASH }
  
  (* negative action *)
  | '~' { T.TILDE }
  
  (* sequencing operators *)
  | "||"  { T.PIPE_PIPE }
  | ';'   { T.SEMICOLON }
  | ">>"  { T.GT_GT }
  | "|>"  { T.PIPE_GT }
  
  (* pattern symbols *)
  | "_"  { T.UNDERSCORE }
  
  | "| "  { T.PIPE }
  | "<- " { T.LT_MINUS }
  | "-> " { T.MINUS_GT }
  | '('   { T.LPAREN }
  | ')'   { T.RPAREN }
  | '{'   { T.LBRACE }
  | '}'   { T.RBRACE }
  | '['	  { T.LBRACKET }
  | ']'	  { T.RBRACKET }
  | '<'	  { T.LANGLE }
  | '>'	  { T.RANGLE }
  | '.'   { T.DOT }
  | ','   { T.COMMA }
  | ':'   { T.COLON }
  | ":="  { T.COLON_EQ }

  | impl_name { scan_impl lexbuf }
  | symbolic_name { scan_sym lexbuf }
  | '\n' {Lexing.new_line lexbuf; main lexbuf}
  | eof  {T.EOF}
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
