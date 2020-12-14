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
  | "Owned"        { OWNED }
  (* | "Unowned"      { UNOWNED } *)
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
  (* | pid            { PID (Lexing.lexeme lexbuf) } *)
  | id             { ID (Lexing.lexeme lexbuf) }
  | _              { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof            { EOF }
(* stealing from Core parser *)
  (* | "_Atomic"      { ATOMIC       } *)
  | "_Bool"        { BOOL         }
  | "char"         { CHAR         }
  (* | "double"       { DOUBLE       } *)
  (* | "enum"         { ENUM         } *)
  (* | "float"        { FLOAT        } *)
  | "int"          { INT          }
  | "ichar"        { ICHAR        }
  | "long"         { LONG         }
  (* | "long_double"  { LONG_DOUBLE  } *)
  | "long_long"    { LONG_LONG    }
  | "short"        { SHORT        }
  | "signed"       { SIGNED       }
  (* | "struct"       { STRUCT       }
   * | "union"        { UNION        } *)
  | "unsigned"     { UNSIGNED     }
  (* | "void"         { VOID         } *)
  | "int8_t"       { INT8_T       }
  | "int16_t"      { INT16_T      }
  | "int32_t"      { INT32_T      }
  | "int64_t"      { INT64_T      }
  | "uint8_t"      { UINT8_T      }
  | "uint16_t"     { UINT16_T     }
  | "uint32_t"     { UINT32_T     }
  | "uint64_t"     { UINT64_T     }
  | "intptr_t"     { INTPTR_T     }
  | "intmax_t"     { INTMAX_T     }
  | "uintptr_t"    { UINTPTR_T    }
  | "uintmax_t"    { UINTMAX_T    }
  | "size_t"       { SIZE_T       }
  | "ptrdiff_t"    { PTRDIFF_T    }
  (* | "["            { LBRACKET     }
   * | "]"            { RBRACKET     } *)
