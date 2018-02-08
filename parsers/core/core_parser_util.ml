type _sym =
  string * (Lexing.position * Lexing.position)

let _sym_compare (str1, _) (str2, _) =
  compare str1 str2

let pp_pos (_, (start_p, end_p)) =
  let filename = Filename.basename start_p.Lexing.pos_fname in
  let (l1, l2) = (start_p.Lexing.pos_lnum, end_p.Lexing.pos_lnum) in
  
  let c1 = start_p.Lexing.pos_cnum - start_p.Lexing.pos_bol in
  let c2 = end_p.Lexing.pos_cnum - end_p.Lexing.pos_bol in
  
  if l1 = l2 then
    Printf.sprintf "%s:%d:%d-%d" filename l1 c1 c2
  else
    Printf.sprintf "%s:%d:%d - %d:%d" filename l1 c1 l2 c2


type mode =
  | StdMode
  | ImplORFileMode



(* Type of Core parser outputs *)
type result =
    (* main symbol, globals, fun_map *)
  | Rfile of Symbol.sym * (Symbol.sym * Core.core_base_type * unit Core.expr) list * unit Core.fun_map
  | Rstd  of (string, Symbol.sym) Pmap.map (* Map of ailnames *) * unit Core.fun_map
  | Rimpl of Core.impl (* * unit Core.fun_map *)


type token =
  | SHORT
  | INT
  | LONG
  | LONG_LONG
  | BOOL
  | SIGNED
  | UNSIGNED
  | FLOAT
  | DOUBLE
  | LONG_DOUBLE
  | CHAR
  | ICHAR
  | VOID
  
  | INT8_T
  | INT16_T
  | INT32_T
  | INT64_T
  | UINT8_T
  | UINT16_T
  | UINT32_T
  | UINT64_T

  | INTPTR_T
  | INTMAX_T
  | UINTPTR_T
  | UINTMAX_T
  
  | SIZE_T
  | PTRDIFF_T
  
  | ATOMIC
  | STRUCT (* TODO *)
  | UNION (* TODO *)
  | ENUM (* TODO *)
  | WCHAR_T
  | CHAR16_T
  | CHAR32_T
  | INTEGER
  | FLOATING
  | BOOLEAN
  | POINTER
  | CTYPE
  | CFUNCTION
  | UNIT
  | UNIT_VALUE
  | EFF
  | LIST
  | TRUE
  | FALSE
  | NOT
  | UNDEF
  | ERROR
  | SKIP
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | UNSEQ
  | WEAK
  | STRONG
  | ATOM
  | SAVE
  | RUN
  | RAISE
  | REGISTER
(*
  | TRY
  | WITH
*)

  | INDET
  | BOUND
  | CREATE
  | ALLOC
  | KILL
  | STORE
  | LOAD
  | RMW
  | FENCE
  | DEF
  | GLOB
  | FUN
  | PROC
  | END
  | SEQ_CST
  | RELAXED
  | RELEASE
  | ACQUIRE
  | CONSUME
  | ACQ_REL
  | IS_SCALAR
  | IS_INTEGER
  | IS_SIGNED
  | IS_UNSIGNED
  | IS_UNSPEC
  | UNSPECIFIED
  
  | STRING of string
  | CSTRING of string
  
  | SYM of _sym
  | IMPL of Implementation_.implementation_constant
  | UB of Undefined.undefined_behaviour
  | INT_CONST of Nat_big_num.num
  
  | BANG
  
  | CASE
  | OF
  
  | EQ_GT

  | PLUS
  | MINUS
  | STAR
  | SLASH
(*  | PERCENT *)
  | REM_T
  | REM_F
  | CARET
  | EQ
  | GT
  | LT
  | GE
  | LE
  | SLASH_BACKSLASH
  | BACKSLASH_SLASH
  | NEG
  | PIPES
  | UNDERSCORE
  | PIPE
  | MINUS_GT
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACES
  | RBRACES
  | LBRACKET
  | RBRACKET
  | LANGLE
  | RANGLE
  | DOT
  | DOTS
  | SEMICOLON
  | COMMA
  | COLON
  | COLON_EQ
  | EOF
  | PIPE_PIPE
  
  | PAR
  | ND
  | WAIT
  | ARRAY_SHIFT
  | MEMBER_SHIFT
  
  (* integer values *)
  | IVMAX
  | IVMIN
  | IVSIZEOF
  | IVALIGNOF
  | CCALL
  | PCALL
  | CFUNCTION_VALUE

  | COLON_COLON
  | BRACKETS
  | ARRAY
  | LOADED
  | SPECIFIED
  
  | PURE
  
  | MEMOP
  | MEMOP_OP of Mem_common.memop
  
  | AILNAME

(*
  | UNION
  | UNDEF
  | TRUE
  | THEN
  | STRUCT
  | STORE
  | SKIP
  | SIZE_T
  | SIGNED
  | SHORT
  | OF
  | NOT
  | NAME of Core.name
  | LONG_LONG
  | LONG_DOUBLE
  | LONG
  | LOAD
  | COMPARE_EXCHANGE_STRONG
  | COMPARE_EXCHANGE_WEAK
  | LET
  | KILL
  | INT
  | IN
  | IF
  | ICHAR
  | FUN
  | EXCLAM
  | ERROR
  | ENUM
  | END
  | ELSE
  | DOUBLE
  | DEF
  | CTYPE
  | CREATE
  | COMPLEX
  | CHAR32_T
  | CHAR16_T
  | CHAR
  | CASE
  | BOOLEAN
  | BOOL
  | ALLOC
  | ADDRESS
 *)
