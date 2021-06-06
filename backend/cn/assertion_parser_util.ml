(* adapting from core_parser_util *)

type token =
  | Z of Z.t
  | NAME of string

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | POWER

  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

  | LPAREN
  | RPAREN
  | COMMA

  | QUESTION
  | COLON


  | MEMBER of string
  | DOTDOT

  | POINTERCAST
  | INTEGERCAST

  | AMPERSAND
  | AT

  | EOF
