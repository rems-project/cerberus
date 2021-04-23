(* adapting from core_parser_util *)

type token =
  | Z of Z.t
  | NAME of string

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | POWER

  | PLUSDOT
  | MINUSDOT
  | STARDOT

  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

  | LPAREN
  | RPAREN
  | COMMA
  | POINTERCAST

  | AMPERSAND
  | AT

  | EOF
