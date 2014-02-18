open Global

(* Type of Core parser outputs *)
type result =
  | Rfile of Core.sym * (zero Core.fun_map)
  | Rstd  of zero Core.fun_map
  | Rimpl of zero Core.impl


type token =
  | ATOMIC
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
  | STRUCT
  | UNION
  | ENUM
  | SIZE_T
  | INTPTR_T
  | WCHAR_T
  | CHAR16_T
  | CHAR32_T
  | INTEGER
  | BOOLEAN
  | ADDRESS
  | CTYPE
  | UNIT
  | FUNCTION
  | NULL
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
  | WEAK
  | STRONG
  | ATOM
  | SAVE
  | RUN
  | RETURN
  | INDET
  | CREATE
  | ALLOC
  | KILL
  | STORE
  | LOAD
  | COMPARE_EXCHANGE_STRONG
  | COMPARE_EXCHANGE_WEAK
  | DEF
  | FUN
  | PROC
  | END
  | CASE
  | OF
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

  | SYM of string
  | IMPL of Implementation_.implementation_constant
  | UB of Undefined.undefined_behaviour
  | INT_CONST of Big_int.big_int
  
  | DQUOTE
  
  | CASE_TY
  | SIGNED_PATTERN
  | UNSIGNED_PATTERN
  | ARRAY_PATTERN
  | POINTER_PATTERN
  | ATOMIC_PATTERN
  | EQ_GT

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | PERCENT
  | EQ
  | LT
  | LE
  | SLASH_BACKSLASH
  | BACKSLASH_SLASH
  | TILDE
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
  | COMMA
  | COLON
  | COLON_EQ
  | EOF
  | SEMICOLON
  | PIPE_PIPE


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
