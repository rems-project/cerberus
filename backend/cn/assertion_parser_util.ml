(* adapting from core_parser_util *)

type token =
  | Z of Z.t
  | LNAME of string
  | UNAME of string
  | MEMBER of string
  | OARG of string

  | TRUE
  | FALSE

  | LET
  | EQUAL
  | UNCHANGED

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | POWER
  | MOD
  | REM
  | DIVISIBLE

  | FLIPBIT

  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE
  | RBRACE
  | COMMA
  | SEMICOLON

  | QUESTION
  | COLON
  | OR
  | AND
  | NOT

  | NULL
  | OFFSETOF

  | CELLPOINTER
  | DISJOINT


  | POINTERCAST
  | INTEGERCAST
  | POINTER
  | INTEGER

  | AMPERSAND
  | AT

  | EACH
  | FOR
  | BLAST

  | WHERE
  | WITH
  | TYP
  | TYPEOF
  | IF
  | STRUCT

  | EOF
