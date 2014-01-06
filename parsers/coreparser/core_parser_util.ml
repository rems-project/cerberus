open Global

(* Type of Core parser outputs *)
type result =
  | Rfile of Core.sym * (zero Core.fun_map)
  | Rstd  of zero Core.fun_map
  | Rimpl of zero Core.impl


type token = 
  | WCHAR_T
  | VOID
  | UNSIGNED
  | UNIT
  | UNION
  | UNDERSCORE
  | UNDEF
  | TRUE
  | TILDE
  | THEN
  | SYM of string
  | STRUCT
  | STORE
  | STAR
  | SLASH_BACKSLASH
  | SLASH
  | SKIP
  | SIZE_T
  | SIGNED
  | SHORT
  | SEMICOLON
  | SAVE
  | SAME
  | RUN
  | RPAREN
  | RET
  | RBRACKET
  | RBRACE
  | RANGLE
  | PROC
  | PLUS
  | PIPE_PIPE
  | PIPE_GT
  | PIPE
  | PERCENT
  | OF
  | NOT
  | NAME of Core.name0
  | MINUS_GT
  | MINUS
  | LT_MINUS
  | LT
  | LPAREN
  | LONG_LONG
  | LONG_DOUBLE
  | LONG
  | LOAD
  | COMPARE_EXCHANGE_STRONG
  | COMPARE_EXCHANGE_WEAK
  | LET
  | LE
  | LBRACKET
  | LBRACE
  | LANGLE
  | KILL
  | INT_CONST of Big_int.big_int
  | INTPTR_T
  | INTEGER
  | INT
  | IN
  | IMPL of Implementation_.implementation_constant
  | IF
  | ICHAR
  | GT_GT
  | FUN
  | FLOAT
  | FALSE
  | EXCLAM
  | ERROR
  | EQ
  | EOF
  | ENUM
  | END
  | ELSE
  | DOUBLE
  | DOT
  | DEF
  | CTYPE
  | CREATE
  | COMPLEX
  | COMMA
  | COLON_EQ
  | COLON
  | CHAR32_T
  | CHAR16_T
  | CHAR
  | CASE
  | BOOLEAN
  | BOOL
  | BACKSLASH_SLASH
  | ATOMIC
  | ALLOC
  | ADDRESS
  | IS_SCALAR
  | IS_INTEGER
  | IS_SIGNED
  | IS_UNSIGNED
  | SEQ_CST
  | RELAXED
  | RELEASE
  | ACQUIRE
  | CONSUME
  | ACQ_REL
  | LBRACES
  | RBRACES
  | PIPES
