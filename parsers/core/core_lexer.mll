{
open Cerb_frontend

exception Error of Errors.core_lexer_cause

module T = Core_parser_util
type token = T.token

let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Stdlib.compare)
    [
      (* for Core ctypes *)
      ("const",       T.CONST      );
      ("_Atomic",     T.ATOMIC     );
      ("_Bool",       T.BOOL       );
      ("char",        T.CHAR       );
      ("double",      T.DOUBLE     );
      (* ("enum",        T.ENUM       ); *)
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
      ("int8_t",      T.INT8_T     );
      ("int16_t",     T.INT16_T    );
      ("int32_t",     T.INT32_T    );
      ("int64_t",     T.INT64_T    );
      ("uint8_t",     T.UINT8_T    );
      ("uint16_t",    T.UINT16_T   );
      ("uint32_t",    T.UINT32_T   );
      ("uint64_t",    T.UINT64_T   );
      ("intptr_t",    T.INTPTR_T   );
      ("intmax_t",    T.INTMAX_T   );
      ("uintptr_t",   T.UINTPTR_T  );
      ("uintmax_t",   T.UINTMAX_T  );
      ("size_t",      T.SIZE_T     );
      ("ptrdiff_t",   T.PTRDIFF_T  );
      
      (* for Core object types *)
      ("integer",   T.INTEGER  );
      ("floating",  T.FLOATING );
      ("pointer",   T.POINTER  );
      ("array",     T.ARRAY    );
      ("cfunction", T.CFUNCTION);
      
      (* for Core base types *)
      ("unit",     T.UNIT   );
      ("boolean",  T.BOOLEAN);
      ("ctype",    T.CTYPE  );
      ("loaded",   T.LOADED );
      ("storable", T.STORABLE);
      
      (* for Core types *)
      ("eff", T.EFF);
      
      (* for Core values *)
      ("NULL",        T.NULL           );
      ("Unit",        T.UNIT_VALUE     );
      ("True",        T.TRUE           );
      ("False",       T.FALSE          );
      ("Ivmax",       T.IVMAX          );
      ("Ivmin",       T.IVMIN          );
      ("Ivsizeof",    T.IVSIZEOF       );
      ("Ivalignof",   T.IVALIGNOF      );
      ("IvCOMPL",     T.IVCOMPL        );
      ("IvAND",       T.IVAND          );
      ("IvOR",        T.IVOR           );
      ("IvXOR",       T.IVXOR          );
      ("Specified",   T.SPECIFIED      );
      ("Unspecified", T.UNSPECIFIED    );
      ("Cfunction",   T.CFUNCTION_VALUE);
      ("Array",       T.ARRAYCTOR      );

      ("Fvfromint",   T.FVFROMINT      );
      ("Ivfromfloat", T.IVFROMFLOAT    );

      (* this is a fake constructor at the syntax level *)
      (* NOTE: it would be better to pass to the Core parser an env with the C types symbols (to resolve max_align_t) *)
      ("IvMaxAlignment", T.IVMAX_ALIGNMENT);
      
      (* for Core (pure) expressions *)
      ("not",          T.NOT         );
      ("undef",        T.UNDEF       );
      ("error",        T.ERROR       );
      ("let",          T.LET         );
      ("in",           T.IN          );
      ("if",           T.IF          );
      ("then",         T.THEN        );
      ("else",         T.ELSE        );
      ("pure",         T.PURE        );
      ("unseq",        T.UNSEQ       );
      ("weak",         T.WEAK        );
      ("strong",       T.STRONG      );
      ("save",         T.SAVE        );
      ("run",          T.RUN         );
      ("bound",        T.BOUND       );
      ("nd",           T.ND          );
      ("par",          T.PAR         );
      ("array_shift",  T.ARRAY_SHIFT );
      ("member_shift", T.MEMBER_SHIFT);
      ("case",         T.CASE        );
      ("of"  ,         T.OF          );
      ("end" ,         T.END         );
      ("pcall",        T.PCALL       );
      ("ccall",        T.CCALL       );
      ("memop",        T.MEMOP       );

      (* Core (pure) builtins for bounded intger arithmetic *)
      ("__conv_int__", T.CONV_INT);
      ("wrapI_add", T.(WRAPI Core.IOpAdd));
      ("wrapI_sub", T.(WRAPI Core.IOpSub));
      ("wrapI_mul", T.(WRAPI Core.IOpMul));
      ("wrapI_shl", T.(WRAPI Core.IOpShl));
      ("wrapI_shr", T.(WRAPI Core.IOpShr));
      ("catch_exceptional_condition_add", T.(CATCH_EXCEPTIONAL_CONDITION Core.IOpAdd));
      ("catch_exceptional_condition_sub", T.(CATCH_EXCEPTIONAL_CONDITION Core.IOpSub));
      ("catch_exceptional_condition_mul", T.(CATCH_EXCEPTIONAL_CONDITION Core.IOpMul));
      ("catch_exceptional_condition_shl", T.(CATCH_EXCEPTIONAL_CONDITION Core.IOpShl));
      ("catch_exceptional_condition_shr", T.(CATCH_EXCEPTIONAL_CONDITION Core.IOpShr));
      
      (* for Core.action_ *)
      ("create", T.CREATE);
      ("create_readonly", T.CREATE_READONLY);
      ("alloc",  T.ALLOC );
      ("free",   T.FREE  );
      ("kill",   T.KILL  );
      ("store",  T.STORE );
      ("store_lock",  T.STORE_LOCK );
      ("load",   T.LOAD  );
      ("seq_rmw",   T.SEQ_RMW  );
      ("seq_rmw_with_forward",   T.SEQ_RMW_WITH_FORWARD  );
      ("rmw",    T.RMW   );
      ("fence",  T.FENCE );
(*      ("compare_exchange_strong",  T.COMPARE_EXCHANGE_STRONG); *)
      
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
      ("are_compatible", T.ARE_COMPATIBLE);
      
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
      ("PtrWellAligned",   T.MEMOP_OP Mem_common.PtrWellAligned  );
      ("PtrArrayShift",    T.MEMOP_OP Mem_common.PtrArrayShift   );
      ("PtrMemberShift",   T.PTRMEMBERSHIFT);
      
      ("Memcpy",        T.MEMOP_OP Mem_common.Memcpy       );
      ("Memcmp",        T.MEMOP_OP Mem_common.Memcmp       );
      ("Realloc",       T.MEMOP_OP Mem_common.Realloc      );
      ("Va_start",      T.MEMOP_OP Mem_common.Va_start     );
      ("Va_copy",       T.MEMOP_OP Mem_common.Va_copy      );
      ("Va_arg",        T.MEMOP_OP Mem_common.Va_arg       );
      ("Va_end",        T.MEMOP_OP Mem_common.Va_end       );
      ("Copy_alloc_id", T.MEMOP_OP Mem_common.Copy_alloc_id);
      
      (* for source attributes *)
      ("ailname", T.AILNAME);

      ("ail_ctype", T.AILCTYPE);

      (* for core builtins *)
      ("builtin", T.BUILTIN);
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
    T.IMPL (Pmap.find id Implementation.impl_map)
  with Not_found ->
    match Cerb_util.remove_prefix ~prefix:"<builtin_" ~trim_end:1 id with
      | Some str ->
          T.IMPL (Implementation.BuiltinFunction str)
      | None ->
          raise (Error (Core_lexer_invalid_implname id))


let scan_ub lexbuf =
  let id = Lexing.lexeme lexbuf in
  match Bimap.lookupR compare compare (String.sub id 2 (String.length id - 4)) Undefined.ub_str_bimap with
    | Some ub ->
        T.UB ub
    | None ->
        begin match Cerb_util.remove_prefix ~prefix:"<<DUMMY(" ~trim_end:3 id with
          | Some str ->
              T.UB (Undefined.DUMMY str)
          | None ->
              raise (Error (Core_lexer_invalid_ubname id))
        end
    | exception _ ->
        raise (Error (Core_lexer_invalid_ubname id))




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
  "<<" ( ['A'-'Z' 'a'-'z' '_' '0'-'9']* | "DUMMY" "(" ['A'-'Z' 'a'-'z' '_' ' ' '.' ':' '-' '=' '<' '>' '0'-'9' '(' ')']* ")" )  ">>"
let impl_name =
  '<' ['A'-'Z' 'a'-'z' '_' '.' '0'-'9']* '>'
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

  | error_name
      { let str = Lexing.lexeme lexbuf in
        T.STRING (String.sub str 3 (String.length str - 6))  }
  | ub_name { scan_ub lexbuf }
  | impl_name { scan_impl lexbuf }
  
  (* binary operators *)
  | '+'   { T.PLUS }
  | '-'   { T.MINUS }
  | '*'   { T.STAR }
  | '/'   { T.SLASH }
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
  
  (* list symbols *)
  | "::" { T.COLON_COLON }
  | "[]" { T.BRACKETS }
  
  (* pattern symbols *)
  | "_"  { T.UNDERSCORE }
  
  | "| "  { T.PIPE }
  | '('   { T.LPAREN }
  | ')'   { T.RPAREN }
  | '['   { T.LBRACKET }
  | ']'   { T.RBRACKET }
  | '{'   { T.LBRACE }
  | '}'   { T.RBRACE }
  | "..." { T.DOTS }
  | "."   { T.DOT }
  | ";"   { T.SEMICOLON }
  | ','   { T.COMMA }
  | ':'   { T.COLON }
  | ":="  { T.COLON_EQ }
  | "'"   { T.SQUOTE }
  
  | "=>" { T.EQ_GT }
  
  | symbolic_name { scan_sym lexbuf }
  | '\n' {Lexing.new_line lexbuf; main lexbuf}
  | eof  {T.EOF}
  | _ as c
    { raise (Error (Core_lexer_invalid_symbol c)) }


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
