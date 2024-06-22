{
open Cerb_frontend

open Cn_tokens

exception Cn_lexer_error

let keywords: (string * Cn_tokens.token) list = [
  "accesses", CN_ACCESSES;
  "alloc_id", CN_ALLOC_ID;
  "apply", CN_APPLY;
  "array_shift", CN_ARRAY_SHIFT;
  "assert", ASSERT;
  "Block", CN_BLOCK;
  "bool", CN_BOOL; (* shared with C23 *)
  "boolean", CN_BOOL; (* TODO(Christopher/Dhruv): are all these variants of BOOL needed? *)
  "CN_bool", CN_BOOL; (* TODO(Christopher/Dhruv): are all these variants of BOOL needed? *)
  "cn_function", CN_FUNCTION; (* TODO(Christopher/Dhruv): is this variant still needed? *)
  "datatype", CN_DATATYPE;
  "default", DEFAULT; (* shared with C11 *)
  "each", CN_EACH;
  "else", ELSE; (* shared with C11 *)
  "ensures", CN_ENSURES;
  "extract", CN_EXTRACT;
  "false", CN_FALSE;
  "function", CN_FUNCTION;
  "good", CN_GOOD;
  "have", CN_HAVE;
  "i128", CN_BITS (`I,128);
  "i16", CN_BITS (`I,16);
  "i32", CN_BITS (`I,32);
  "i64", CN_BITS (`I,64);
  "i8", CN_BITS (`I,8);
  "if", IF; (* shared with C11 *)
  "inline", INLINE; (* shared with C11 *)
  "instantiate", CN_INSTANTIATE;
  "integer", CN_INTEGER;
  "inv", CN_INV;
  "lemma", CN_LEMMA;
  "let", CN_LET;
  "list", CN_LIST;
  "map", CN_MAP;
  "match", CN_MATCH;
  "member_shift", CN_MEMBER_SHIFT;
  "NULL", CN_NULL;
  "offsetof", OFFSETOF;
  "Owned", CN_OWNED;
  "pack", CN_PACK;
  "pointer", CN_POINTER;
  "predicate", CN_PREDICATE;
  "print", CN_PRINT;
  "real", CN_REAL;
  "requires", CN_REQUIRES;
  "return", RETURN; (* shared with C11 *)
  "set", CN_SET;
  "sizeof", SIZEOF; (* shared with C11 *)
  "spec", CN_SPEC;
  "split_case", CN_SPLIT_CASE;
  "struct", STRUCT; (* shared with C11 *)
  "take", CN_TAKE;
  "true", CN_TRUE;
  "trusted", CN_TRUSTED;
  "tuple", CN_TUPLE;
  "type_synonym", CN_TYPE_SYNONYM;
  "u128", CN_BITS (`U,128);
  "u16", CN_BITS (`U,16);
  "u32", CN_BITS (`U,32);
  "u64", CN_BITS (`U,64);
  "u8", CN_BITS (`U,8);
  "unchanged", CN_UNCHANGED;
  "unfold", CN_UNFOLD;
  "unpack", CN_UNPACK;
  "void", VOID; (* shared with C11 *)
]

let lexicon: (string, token) Hashtbl.t =
  let lexicon = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add lexicon key builder in
  List.iter add keywords; lexicon

let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  if ch = '\n' then Lexing.new_line lexbuf;
  remainder lexbuf

}

(* ========================================================================== *)

(* Integer constant - we follow C but omit suffixes (see ISO C11 §6.4.4.1#1) *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let octal_digit = ['0'-'7']
let nonzero_digit = ['1'-'9']

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant = hexadecimal_prefix hexadecimal_digit+

(* C23 binary constant, but omitting ' separators for now *)
(* TODO(Christopher/Dhruv): add support for ' separators to be in line with C23 ? *)
let binary_prefix = "0b" | "0B"
let binary_digit = "0" | "1"
let binary_constant =
  (* binary_prefix (binary_digit "'"?)+ *)
  binary_prefix (binary_digit)+

let octal_constant = '0' octal_digit*
let decimal_constant = nonzero_digit digit*

let integer_constant =
    decimal_constant
  | octal_constant
  | hexadecimal_constant
  | binary_constant

(* Identifiers - we follow C11 *)
(* TODO(Christopher/Dhruv): do you care about following C11 closely for this
    (e.g. with respect to the universal character stuff), or should we simplify
    like we already do for uppercase names. *)
(* see ISO C11 §6.4.3#1 *)
let hex_quad =
  hexadecimal_digit hexadecimal_digit
    hexadecimal_digit hexadecimal_digit

let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

(* see ISO C11 §6.4.4.1#1 *)
let nondigit = ['_' 'a'-'z' 'A'-'Z']
let identifier_nondigit =
    nondigit
  | universal_character_name
let identifier = identifier_nondigit (identifier_nondigit | digit)*


(* Whitespaces *)
let whitespace_char = [' ' '\t' (*'\n'*) '\012' '\r']

let integer_width = ("8" | "16" | "32" | "64" | "128")

(* ========================================================================== *)

rule onelinecomment = parse
  | '\n' | eof { () }
  | _          { lex_comment onelinecomment lexbuf }

(* Entry point *)
and initial = parse
  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; initial lexbuf}

  | '\n'             { Lexing.new_line lexbuf; initial lexbuf }
  | whitespace_char+ { initial lexbuf }

  | (integer_constant as str) 'u' (integer_width as n)
      { CN_CONSTANT (str, `U, int_of_string n) }
  | (integer_constant as str) 'i' (integer_width as n)
      { CN_CONSTANT (str, `I, int_of_string n) }
  | (integer_constant as str)
      (* TODO(K): (!!!) when moving away froms Cabs.constant in this token, be careful about the
          decoding of octal constants. Z.of_string won't do the right (C behaviour) thing. *)
      { CONSTANT (Cabs.CabsInteger_const (str, None)) }

  (* Punctuators *)
  | '['   { LBRACK              }
  | ']'   { RBRACK              }
  | '('   { LPAREN              }
  | ')'   { RPAREN              }
  | '{'   { LBRACE              }
  | '}'   { RBRACE              }
  | '.'   { DOT                 }
  | "->"  { MINUS_GT            }
  | '&'   { AMPERSAND           }
  | '*'   { STAR                }
  | '+'   { PLUS                }
  | '-'   { MINUS               }
  | '!'   { BANG                }
  | '/'   { SLASH               }
  | '%'   { PERCENT             }
  | '<'   { LT                  }
  | '>'   { GT                  }
  | "<="  { LT_EQ               }
  | ">="  { GT_EQ               }
  | "=="  { EQ_EQ               }
  | "!="  { BANG_EQ             }
  | "&&"  { AMPERSAND_AMPERSAND }
  | "||"  { PIPE_PIPE           }
  | '?'   { QUESTION            }
  | ':'   { COLON               }
  | ';'   { SEMICOLON           }
  | '='   { EQ                  }
  | ','   { COMMA               }
  | "_"   { CN_WILD             }

    (* copied over from backend/cn/assertion_lexer.mll *)
  | ['A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as id
      { try
          Hashtbl.find lexicon id
        with Not_found ->
          UNAME id
      }

  | identifier as id
    { try
        Hashtbl.find lexicon id
      with Not_found ->
        LNAME id
    }
  | eof
      { EOF }
  | _
      { raise Cn_lexer_error }

(* ========================================================================== *)

{

}
