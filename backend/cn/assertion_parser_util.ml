(* adapting from core_parser_util *)

type token =
  | Z of Z.t
  | NAME of string

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

  | AMPERSAND
  | AT

  | EACH

  | EOF
