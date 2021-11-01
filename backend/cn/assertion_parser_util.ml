(* adapting from core_parser_util *)

type token =
  | Z of Z.t
  | NAME of string

  | VAR
  | EQUAL

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | POWER
  | PERCENT

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

  | NULL
  | OFFSETOF


  | MEMBER of string
  | DOTDOT

  | POINTERCAST
  | INTEGERCAST
  | POINTER
  | INTEGER

  | AMPERSAND
  | AT

  | EACH

  | EOF
