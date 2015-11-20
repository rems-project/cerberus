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
      ("_Bool",       T.BOOL);
      ("signed",      T.SIGNED);
      ("unsigned",    T.UNSIGNED);
      ("float",       T.FLOAT);
      ("double",      T.DOUBLE);
      ("long_double", T.LONG_DOUBLE);
(*      ("_Complex",    T.COMPLEX); *)
      ("char",        T.CHAR);
      ("ichar",       T.ICHAR);
      ("void",        T.VOID);
      ("struct",      T.STRUCT);
      ("union",       T.UNION);
      ("enum",        T.ENUM);
(*
      ("size_t",      T.SIZE_T);
      ("intptr_t",    T.INTPTR_T);
      ("ptrdiff_t",   T.PTRDIFF_T);
      ("wchar_t",     T.WCHAR_T);
      ("char16_t",    T.CHAR16_T);
      ("char32_t",    T.CHAR32_T);
      
      ("int8_t",    T.INT8_T);
      ("int16_t",   T.INT16_T);
      ("int32_t",   T.INT32_T);
      ("int64_t",   T.INT64_T);
      ("uint8_t",   T.UINT8_T);
      ("uint16_t",  T.UINT16_T);
      ("uint32_t",  T.UINT32_T);
      ("uint64_t",  T.UINT64_T);
*)
      
      
      
      (* for Core.core_base_type *)
      ("integer",   T.INTEGER  );
      ("boolean",   T.BOOLEAN  );
      ("pointer",   T.POINTER  );
      ("ctype",     T.CTYPE    );
      ("cfunction", T.CFUNCTION);
      ("unit",      T.UNIT     );
      ("function",  T.FUNCTION );
      
      ("eff", T.EFF);
(*    | Tuple of list core_base_type *)
      
      (* for Core.expr *)
      ("list",   T.LIST     );
      ("cons",   T.CONS     );
      ("array",   T.ARRAY     );
      ("true",   T.TRUE);
      ("false",  T.FALSE);
(*  | Econst of Cmm_aux.constant *)
(*  | Ectype of ctype *)
(*  | Eaddr of Memory.mem_addr *)
(*  | Esym of sym *)
(*  | Eimpl of Implementation_.implementation_constant *)
(*  | Etuple of list (expr 'a) *)
      ("not", T.NOT);
(*  | Eop of binop * expr 'a * expr 'a *)
(*  | Ecall of name * list (expr 'a) *)
      ("undef", T.UNDEF);
      ("error", T.ERROR);
      ("skip", T.SKIP);
      ("let", T.LET);
      ("in", T.IN);
      ("if", T.IF);
      ("then", T.THEN);
      ("else", T.ELSE);
(*  | Eproc of set 'a * name * list (expr 'a) *)
(*  | Eaction of paction 'a *)
(*  | Eunseq of list (expr 'a) *)
      ("unseq", T.UNSEQ);
      ("weak", T.WEAK);
      ("strong", T.STRONG);
      ("atom", T.ATOM);
      ("save", T.SAVE);
      ("run", T.RUN);
      ("indet", T.INDET);
      ("return", T.RETURN);
(*
      ("try", T.TRY);
      ("with", T.WITH);
*)
      ("raise", T.RAISE);
      ("register", T.REGISTER);
  
      ("nd", T.ND);
      ("par", T.PAR);
      ("wait", T.WAIT);

     
      ("array_shift", T.ARRAY_SHIFT);
      ("member_shift", T.MEMBER_SHIFT);
      
      (* for Core.action_ *)
      ("create",  T.CREATE);
      ("alloc",   T.ALLOC );
      ("kill",    T.KILL  );
      ("store",   T.STORE );
      ("load",    T.LOAD  );
      ("rmw",     T.RMW   );
     
      
      
      ("def",     T.DEF     ); (* for implementation files only *)
      ("glob",    T.GLOB     ); (* for implementation files only *)
      ("fun",     T.FUN     );
      ("proc",    T.PROC     );
      
      
      ("end",     T.END     );
      ("seq_cst", T.SEQ_CST );
      ("relaxed", T.RELAXED );
      ("release", T.RELEASE );
      ("acquire", T.ACQUIRE );
      ("consume", T.CONSUME );
      ("acq_rel", T.ACQ_REL );

      ("case_list",   T.CASE_LIST);
      ("case_ctype",   T.CASE_CTYPE);


(* TODO: temporary *)
      ("is_scalar",   T.IS_SCALAR  );
      ("is_integer",  T.IS_INTEGER );
      ("is_signed",   T.IS_SIGNED  );
      ("is_unsigned", T.IS_UNSIGNED);
      
      (* integer values *)
      ("ivmax",     T.IVMAX);
      ("ivmin",     T.IVMIN);
      ("ivsizeof",  T.IVSIZEOF);
      ("ivalignof", T.IVALIGNOF);
      ("unspecified", T.UNSPECIFIED);
      
      ("is_unspec", T.IS_UNSPEC);
    ]

let scan_sym lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    Pmap.find id keywords
  with Not_found ->
    T.SYM (id, (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf))

let scan_impl lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    T.IMPL (Pmap.find id Implementation_.impl_map)
  with Not_found ->
    if Str.string_match (Str.regexp "^<std_function_") id 0 then
      T.IMPL (Implementation_.StdFunction (String.sub id 14 (String.length id - 15)))
    else
      failwith ("Found an invalid impl_name: " ^ id)

let scan_ub lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    T.UB (Pmap.find id Undefined.ub_map)
  with Not_found ->
    failwith ("Found an invalid undefined-behaviour: " ^ id)




let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf

}


let error_name = "<<<" ['A'-'Z' 'a'-'z' '_' '0'-'9']* ">>>"
let ub_name = "<<" ['A'-'Z' 'a'-'z' '_' '0'-'9']* ">>"
let impl_name = '<' ['A'-'Z' 'a'-'z' '_' '.']* '>'
let symbolic_name = ['_' 'a'-'z']['0'-'9' 'A'-'Z' 'a'-'z' '_']*

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
  | ['0'-'9']+ as integer
      { T.INT_CONST (Nat_big_num.of_string integer) }
  
  (* binary operators *)
  | '+'   { T.PLUS }
  | '-'   { T.MINUS }
  | '*'   { T.STAR }
  | '/'   { T.SLASH }
(*
  | '%'   { T.PERCENT }
*)
  | "rem_t" { T.REM_T }
  | "rem_f" { T.REM_F }
  | '^'   { T.CARET }
  | '='   { T.EQ }
  | '>'   { T.GT }
  | '<'   { T.LT }
  | ">="  { T.GE }
  | "<="  { T.LE }
  | "/\\" { T.SLASH_BACKSLASH }
  | "\\/" { T.BACKSLASH_SLASH }
  
  (* negative action *)
  | '~' { T.TILDE }
  
  | "||"  { T.PIPE_PIPE }
  | "|||"  { T.PIPES }
  
  (* pattern symbols *)
  | "_"  { T.UNDERSCORE }
  
  | "| "  { T.PIPE }
  | "-> " { T.MINUS_GT }
  | '('   { T.LPAREN }
  | ')'   { T.RPAREN }
  | '{'   { T.LBRACE }
  | '}'   { T.RBRACE }
  | "{{{" { T.LBRACES }
  | "}}}" { T.RBRACES }
  | '['	  { T.LBRACKET }
  | ']'	  { T.RBRACKET }
  | '<'	  { T.LANGLE }
  | '>'	  { T.RANGLE }
  | '.'   { T.DOT }
  | "..." { T.DOTS }
  | ";"   { T.SEMICOLON }
  | ','   { T.COMMA }
  | ':'   { T.COLON }
  | ":="  { T.COLON_EQ }
  | "\""  { T.DQUOTE }
  
  | "=>" { T.EQ_GT }
  
  | error_name { let str = Lexing.lexeme lexbuf in
             T.STRING (String.sub str 3 (String.length str - 6))  }
  
  | ub_name { scan_ub lexbuf }
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
