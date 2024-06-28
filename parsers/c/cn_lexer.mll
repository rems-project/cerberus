{
open Cerb_frontend

open Cn_tokens

exception Cn_lexer_error

let keywords: (string * Cn_tokens.token) list = [
  "accesses", ACCESSES;
  "alloc_id", ALLOC_ID;
  "apply", APPLY;
  "array_shift", ARRAY_SHIFT;
  "assert", ASSERT;
  "Block", BLOCK;
  "bool", BOOL; (* shared with C23 *)
  "boolean", BOOL; (* TODO(Christopher/Dhruv): are all these variants of BOOL needed? *)
  "CN_bool", BOOL; (* TODO(Christopher/Dhruv): are all these variants of BOOL needed? *)
  "cn_function", FUNCTION; (* TODO(Christopher/Dhruv): is this variant still needed? *)
  "datatype", DATATYPE;
  "default", DEFAULT; (* shared with C11 *)
  "each", EACH;
  "else", ELSE; (* shared with C11 *)
  "ensures", ENSURES;
  "extract", EXTRACT;
  "false", FALSE;
  "function", FUNCTION;
  "good", GOOD;
  "have", HAVE;
  "i128", BITS_TYPE (`I,128);
  "i16", BITS_TYPE (`I,16);
  "i32", BITS_TYPE (`I,32);
  "i64", BITS_TYPE (`I,64);
  "i8", BITS_TYPE (`I,8);
  "if", IF; (* shared with C11 *)
  "inline", INLINE; (* shared with C11 *)
  "instantiate", INSTANTIATE;
  "integer", INTEGER;
  "inv", INV;
  "lemma", LEMMA;
  "let", LET;
  "list", LIST;
  "map", MAP;
  "match", MATCH;
  "member_shift", MEMBER_SHIFT;
  "NULL", NULL;
  "offsetof", OFFSETOF;
  "Owned", OWNED;
  "pack", PACK;
  "pointer", POINTER;
  "predicate", PREDICATE;
  "print", PRINT;
  "real", REAL;
  "requires", REQUIRES;
  "return", RETURN; (* shared with C11 *)
  "set", SET;
  "sizeof", SIZEOF; (* shared with C11 *)
  "spec", SPEC;
  "split_case", SPLIT_CASE;
  "struct", STRUCT; (* shared with C11 *)
  "take", TAKE;
  "true", TRUE;
  "trusted", TRUSTED;
  "tuple", TUPLE;
  "type_synonym", TYPE_SYNONYM;
  "u128", BITS_TYPE (`U,128);
  "u16", BITS_TYPE (`U,16);
  "u32", BITS_TYPE (`U,32);
  "u64", BITS_TYPE (`U,64);
  "u8", BITS_TYPE (`U,8);
  "unchanged", UNCHANGED;
  "unfold", UNFOLD;
  "unpack", UNPACK;
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

let relexbuf_opt: (Lexing.lexbuf option) ref =
  ref None

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
      { BITS_CONSTANT (str, `U, int_of_string n) }
  | (integer_constant as str) 'i' (integer_width as n)
      { BITS_CONSTANT (str, `I, int_of_string n) }
  | (integer_constant as str)
      (* TODO(K): (!!!) when moving away froms Cabs.constant in this token, be careful about the
          decoding of octal constants. Z.of_string won't do the right (C behaviour) thing. *)
      { INTEGER_CONSTANT (Cabs.CabsInteger_const (str, None)) }

  | '<' ([^'='][^'<' '>']+ as str) '>'
      {
        try
          LT_CTYPE_GT (C_parser.type_name_eof C_lexer.lexer (Lexing.from_string str))
        with
          | _ ->
              relexbuf_opt := Some (Lexing.from_string (str ^ ">"));
              LT
      }

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
  | "_"   { UNDERSCORE          }

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
let initial lexbuf =
  (* TODO(K) ===> do we need a stack of redos *)
  (* TODO(K) ==> we don't because the ctype regexp excludes any '<' (?) *)
  match !relexbuf_opt with
    | None ->
        initial lexbuf
    | Some relexbuf ->
        begin match initial relexbuf with
          | EOF -> relexbuf_opt := None; initial lexbuf
          | tok -> tok
        end


type lexer_state =
  | LSRegular
  | LSIdentifier of string

let lexer_state = ref LSRegular

let lexer lexbuf : token =
  match !lexer_state with
  | LSRegular ->
      begin match initial lexbuf with
      | LNAME i as tok -> lexer_state := LSIdentifier i; tok
      | UNAME i as tok -> lexer_state := LSIdentifier i; tok
      | _      as tok -> lexer_state := LSRegular; tok
      end
  | LSIdentifier i ->
      lexer_state := LSRegular;
      if Lexer_feedback.is_typedefname i then TYPE else VARIABLE
}
