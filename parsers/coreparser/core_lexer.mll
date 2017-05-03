{
open Pervasives_

module T = Core_parser_util
type token = T.token

let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Pervasives.compare)
    [
      (* for Core ctypes *)
      ("_Atomic",     T.ATOMIC     );
      ("_Bool",       T.BOOL       );
      ("char",        T.CHAR       );
      ("double",      T.DOUBLE     );
      ("enum",        T.ENUM       );
      ("float",       T.FLOAT      );
      ("int",         T.INT        );
      ("ichar",       T.ICHAR      );
      ("long",        T.LONG       );
      ("long_double", T.LONG_DOUBLE);
      ("long_long",   T.LONG_LONG  );
      ("short",       T.SHORT      );
      ("signed",      T.SIGNED     );
      ("struct",      T.STRUCT     );
      ("union",       T.UNION      );
      ("unsigned",    T.UNSIGNED   );
      ("void",        T.VOID       );
      
      (* for Core object types *)
      ("integer",   T.INTEGER  );
      ("floating",  T.FLOATING );
      ("pointer",   T.POINTER  );
      ("cfunction", T.CFUNCTION);
      
      (* for Core base types *)
      ("unit",    T.UNIT   );
      ("boolean", T.BOOLEAN);
      ("ctype",   T.CTYPE  );
      ("list",    T.LIST   );
      ("loaded",  T.LOADED );
      
      (* for Core types *)
      ("eff", T.EFF);
      
      (* for Core values *)
      ("Unit",        T.UNIT_VALUE     );
      ("True",        T.TRUE   );
      ("False",       T.FALSE          );
      ("Ivmax",       T.IVMAX          );
      ("Ivmin",       T.IVMIN          );
      ("Ivsizeof",    T.IVSIZEOF       );
      ("Ivalignof",   T.IVALIGNOF      );
      ("Unspecified", T.UNSPECIFIED    );
      ("Cfunction",   T.CFUNCTION_VALUE);
      ("Nil",         T.NIL            );
      ("Cons",        T.CONS           );
      ("Tuple",  T.TUPLE );
      ("Array",       T.ARRAY          );
      ("Specified",   T.SPECIFIED      );
      
      (* for Core (pure) expressions *)
      ("not",          T.NOT         );
      ("undef",        T.UNDEF       );
      ("error",        T.ERROR       );
      ("skip",         T.SKIP        );
      ("let",          T.LET         );
      ("in",           T.IN          );
      ("if",           T.IF          );
      ("then",         T.THEN        );
      ("else",         T.ELSE        );
      ("pure",         T.PURE        );
      ("unseq",        T.UNSEQ       );
      ("weak",         T.WEAK        );
      ("strong",       T.STRONG      );
      ("atom",         T.ATOM        );
      ("save",         T.SAVE        );
      ("run",          T.RUN         );
      ("indet",        T.INDET       );
      ("bound",        T.BOUND       );
      ("raise",        T.RAISE       );
      ("register",     T.REGISTER    );
      ("nd",           T.ND          );
      ("par",          T.PAR         );
      ("wait",         T.WAIT        );
      ("array_shift",  T.ARRAY_SHIFT );
      ("member_shift", T.MEMBER_SHIFT);
      ("case",         T.CASE        );
      ("of"  ,         T.OF          );
      ("end" ,         T.END         );
      ("pcall",        T.PCALL       );
      ("ccall",        T.CCALL       );
      ("memop",        T.MEMOP       );
      
      (* for Core.action_ *)
      ("create", T.CREATE);
      ("alloc",  T.ALLOC );
      ("kill",   T.KILL  );
      ("store",  T.STORE );
      ("load",   T.LOAD  );
      ("rmw",    T.RMW   );
      ("fence",  T.FENCE );
      
      (* for toplevel declarations *)
      ("def",  T.DEF ); (* for implementation files only *)
      ("glob", T.GLOB);
      ("fun",  T.FUN );
      ("proc", T.PROC);
      
      (* for C11 memory orders *)
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
      
      (* for Memory operations *)
      ("PtrEq",            T.MEMOP_OP Mem_common.PtrEq           );
      ("PtrNe",            T.MEMOP_OP Mem_common.PtrNe           );
      ("PtrLt",            T.MEMOP_OP Mem_common.PtrLt           );
      ("PtrGt",            T.MEMOP_OP Mem_common.PtrGt           );
      ("PtrLe",            T.MEMOP_OP Mem_common.PtrLe           );
      ("PtrGe",            T.MEMOP_OP Mem_common.PtrGe           );
      ("Ptrdiff",          T.MEMOP_OP Mem_common.Ptrdiff         );
      ("IntFromPtr",       T.MEMOP_OP Mem_common.IntFromPtr      );
      ("PtrFromInt",       T.MEMOP_OP Mem_common.PtrFromInt      );
      ("PtrValidForDeref", T.MEMOP_OP Mem_common.PtrValidForDeref);
      
      (* for source attributes *)
      ("ailname", T.AILNAME);
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
  match Bimap.lookupR compare compare (String.sub id 2 (String.length id - 4)) Undefined.ub_str_bimap with
    | Some ub ->
        T.UB ub
    | None ->
        (* TODO: hack *)
        if id = "<<DUMMY>>" then
          T.UB (Undefined.DUMMY "parser")
        else
          failwith ("Found an invalid undefined-behaviour: " ^ id)





let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf
}


(* C-like strings *)
let error_name =
  "<<<" ['A'-'Z' 'a'-'z' '_' '0'-'9']* ">>>"
let ub_name =
  "<<" ['A'-'Z' 'a'-'z' '_' '0'-'9']* ">>"
let impl_name =
  '<' ['A'-'Z' 'a'-'z' '_' '.']* '>'
let symbolic_name =
  ['_' 'a'-'z' 'A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']*

let escape_sequence =
    "\\'" | "\\\"" | "\\?" | "\\\\" | "\\a" | "\\b" | "\\f" | "\\n"
  | "\\r" | "\\t" | "\\v"
let c_char =
    [^ '\'' '\\' '\n']
  | escape_sequence
let character_constant =
  c_char+
let s_char =
    [^ '"' '\\' '\n']
  | escape_sequence

rule cstring = parse
  | s_char as x
      { let xs = cstring lexbuf in
        x :: xs }
  | '"'
      { [] }

and main = parse
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
  (* C-like strings *)
  | '"'
      { let strs = cstring lexbuf in
        (* TODO: check this *)
        T.CSTRING (String.concat "" strs) }
  
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
  | "neg" { T.NEG }
  
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
  | '!'  { T.BANG }
  
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
