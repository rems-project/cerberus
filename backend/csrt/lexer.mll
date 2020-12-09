(* from https://ocaml.org/releases/4.07/htmlman/lexyacc.html *)
(* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
(* https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param *)
(* and from the c and core parsers *)


{
open Lexing
open Tokens


exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let int = '-'? ['0'-'9'] ['0'-'9']*
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let pid = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | "+"            { PLUS }
  | "-"            { MINUS }
  | "*"            { STAR }
  | "&"            { AMPERSAND }
  | "/"            { DIV }
  | "@"            { AT }
  | "("            { LPAREN }
  | ")"            { RPAREN }
  | ","            { COMMA }
  | "<"            { LT }
  | ">"            { GT }
  | "<="           { LE }
  | ">="           { GE }
  | "!="           { NE }
  | "=="           { EQEQ }
  | "min"          { MIN }
  | "max"          { MAX }
  | "."            { DOT }
  | "(integer)"    { POINTER_TO_INTEGER }
  | "(pointer)"    { INTEGER_TO_POINTER }
  | "Block"        { BLOCK }
  | "Unowned"      { UNOWNED }
  | "min"          { MIN }
  | "max"          { MAX }
  | "char"         { CHAR }
  | "short"        { SHORT }
  | "int"          { INT }
  | "long"         { LONG }
  | "signed"       { SIGNED }
  | "unsigned"     { UNSIGNED }
  | white          { read lexbuf }
  | newline        { next_line lexbuf; read lexbuf }
  | int            { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | pid            { PID (Lexing.lexeme lexbuf) }
  | id             { ID (Lexing.lexeme lexbuf) }
  | _              { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof            { EOF }


