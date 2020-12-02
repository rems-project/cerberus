(* from https://ocaml.org/releases/4.07/htmlman/lexyacc.html *)
(* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
(* and from the core_parser *)


{
open Lexing
open Parser

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
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | "+"            { PLUS }
  | "-"            { MINUS }
  | "*"            { STAR }
  | "/"            { DIV }
  | "`div`"        { DIV }
  | "`min`"        { MINIMUM }
  | "`max`"        { MAXIMUM }
  | "("            { LPAREN }
  | ")"            { RPAREN }
  | "<"            { LT }
  | ">"            { GT }
  | "<="           { LE }
  | ">="           { GE }
  | "<>"           { NE }
  | "="            { EQ }
  | "=="           { EQEQ }
  | "."            { DOT }
  | ".."           { DOTDOT }
  | "&"            { AMPERSAND }
  | "it_max u32"   { MAX_U32 }
  | "it_max u64"   { MAX_U64 }
  | "it_min u32"   { MIN_U32 }
  | "it_min u64"   { MIN_U64 }
  | "it_max i32"   { MAX_I32 }
  | "it_max i64"   { MAX_I64 }
  | "it_min i32"   { MIN_I32 }
  | "it_min i64"   { MIN_I64 }
  | white          { read lexbuf }
  | newline        { next_line lexbuf; read lexbuf }
  | int            { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | id             { ID (Lexing.lexeme lexbuf) }
  | _              { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof            { EOF }


