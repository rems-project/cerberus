{
open Cerb_frontend

open Lexing
open Tokens

exception Error of Errors.cparser_cause

type flags = {
  inside_cn : bool;
  magic_comment_char : char;
  at_magic_comments : bool;
}

let offset_location lexbuf pos_fname pos_lnum =
  if pos_lnum > 0 then
    let pos_lnum = pos_lnum - 1 in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname; pos_lnum};
  new_line lexbuf

(* STD §6.4.1#1 *)
let keywords: (string * Tokens.token) list = [
    "auto"           , AUTO;
    "break"          , BREAK;
    "case"           , CASE;
    "char"           , CHAR;
    "const"          , CONST;
    "continue"       , CONTINUE;
    "default"        , DEFAULT;
    "do"             , DO;
    "double"         , DOUBLE;
    "else"           , ELSE;
    "enum"           , ENUM;
    "extern"         , EXTERN;
    "float"          , FLOAT;
    "for"            , FOR;
    "goto"           , GOTO;
    "if"             , IF;
    "inline"         , INLINE;
    "int"            , INT;
    "long"           , LONG;
    "register"       , REGISTER;
    "restrict"       , RESTRICT;
    "return"         , RETURN;
    "short"          , SHORT;
    "signed"         , SIGNED;
    "sizeof"         , SIZEOF;
    "static"         , STATIC;
    "struct"         , STRUCT;
    "switch"         , SWITCH;
    "typedef"        , TYPEDEF;
    "typeof"         , TYPEOF;
    "union"          , UNION;
    "unsigned"       , UNSIGNED;
    "void"           , VOID;
    "volatile"       , VOLATILE;
    "while"          , WHILE;
    "_Alignas"       , ALIGNAS;
    "_Alignof"       , ALIGNOF;
    "_Atomic"        , ATOMIC;
    "_Bool"          , BOOL;
    "_Complex"       , COMPLEX;
    "_Generic"       , GENERIC;
    (* "_Imaginary"     , IMAGINARY; *)
    "_Noreturn"      , NORETURN;
    "_Static_assert" , STATIC_ASSERT;
    "_Thread_local"  , THREAD_LOCAL;

    "assert", ASSERT;
    "offsetof", OFFSETOF;
    "__cerb_va_start", VA_START;
    "__cerb_va_copy", VA_COPY;
    "__cerb_va_arg", VA_ARG;
    "__cerb_va_end", VA_END;

    "__cerb_printtype", PRINT_TYPE;

    "__BMC_ASSUME", BMC_ASSUME;

    (* some GCC extensions *)
    "asm", ASM;
    "__asm__", ASM;
    "__volatile__", ASM_VOLATILE;
    "__builtin_types_compatible_p", BUILTIN_TYPES_COMPATIBLE_P;
    "__builtin_choose_expr", BUILTIN_CHOOSE_EXPR;
  ]

let lexicon: (string, token) Hashtbl.t =
  let lexicon = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add lexicon key builder in
  List.iter add keywords; lexicon


(* BEGIN CN *)

(* CN keywords that are safe for use by all users *)
let cn_keywords: (string * Tokens.token) list = [
    "good"          , CN_GOOD;
    (* "bool"          , CN_BOOL; *) 
    "boolean"       , CN_BOOL;
    (* "CN_bool"       , CN_BOOL; *)
    "integer"       , CN_INTEGER;
    "u8"           , CN_BITS (`U,8);
    "u16"           , CN_BITS (`U,16);
    "u32"           , CN_BITS (`U,32);
    "u64"           , CN_BITS (`U,64);
    "u128"           , CN_BITS (`U,128);
    "i8"           , CN_BITS (`I,8);
    "i16"           , CN_BITS (`I,16);
    "i32"           , CN_BITS (`I,32);
    "i64"           , CN_BITS (`I,64);
    "i128"           , CN_BITS (`I,128);
    "real"          , CN_REAL;
    "pointer"       , CN_POINTER;
    "alloc_id"      , CN_ALLOC_ID;
    "let"           , CN_LET;
    "take"          , CN_TAKE;
    "Owned"         , CN_OWNED;
    "Block"         , CN_BLOCK;
    "each"          , CN_EACH;
    "NULL"          , CN_NULL;
    "true"          , CN_TRUE;
    "false"         , CN_FALSE;
    "requires"      , CN_REQUIRES;
    "ensures"       , CN_ENSURES;
    "inv"           , CN_INV;
    "accesses"      , CN_ACCESSES;
    "trusted"       , CN_TRUSTED;
    "spec"          , CN_SPEC;
    "unchanged"     , CN_UNCHANGED;
    "instantiate"   , CN_INSTANTIATE;
    "split_case"    , CN_SPLIT_CASE;
    "extract"       , CN_EXTRACT;
    "array_shift"   , CN_ARRAY_SHIFT;
    "member_shift"  , CN_MEMBER_SHIFT;
    "unfold"        , CN_UNFOLD;
    "apply"         , CN_APPLY;
    "match"         , CN_MATCH;
    "predicate"     , CN_PREDICATE;
    "function"      , CN_FUNCTION;
    "lemma"         , CN_LEMMA;
    "datatype"      , CN_DATATYPE;
    "type_synonym"  , CN_TYPE_SYNONYM;
    "_"             , CN_WILD;
    "implies"       , CN_IMPLIES;
  ]

(* CN keywords that are functional, but have limitations that make them
unsuitable for non-experts *)
let cn_keywords_experimental: (string * Tokens.token) list = [
    "cn_list"       , CN_LIST; 
    "cn_tuple"      , CN_TUPLE;
    "cn_map"        , CN_MAP;
    "cn_set"        , CN_SET;
    "cn_have"       , CN_HAVE;
    "cn_function"   , CN_FUNCTION;
    "cn_print"      , CN_PRINT;
  ] 

(* CN keywords that are non-functional, but reserved for possible future use *)
let cn_keywords_unimplemented: (string * Tokens.token) list = [
    "pack"          , CN_PACK;
    "unpack"        , CN_UNPACK;
  ]

let cn_lex_builder kw_list : (string, token) Hashtbl.t  = 
  let cn_lex = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add cn_lex key builder in
  List.iter add kw_list; cn_lex

(* 
Attempt to lex a CN keyword. These may be: 
  * 'production' - well-supported and suitable for general use
  * 'experimental' - functional in some cases but not recommended for general use 
  * 'unimplemented' - non-functional, but the keyword is reserved  
*)
let cn_lex_keyword id start_pos end_pos = 
  (* Try to lex CN production keywords *)
  try Hashtbl.find (cn_lex_builder cn_keywords) id
  with Not_found ->
    (* Try to lex CN experimental keywords - warn on success *)
    try 
      let kw = Hashtbl.find (cn_lex_builder cn_keywords_experimental) id in 
      prerr_endline       
        (Pp_errors.make_message
         Cerb_location.(region (start_pos, end_pos) NoCursor)
         Errors.(CPARSER (Errors.Cparser_experimental_keyword id))
         Warning);
      kw 
    with Not_found ->
      try 
        (* Try to lex CN unimplemented keywords - throw an error on success *)
        let _ = Hashtbl.find (cn_lex_builder cn_keywords_unimplemented) id in 
        raise (Error (Errors.Cparser_unimplemented_keyword id))
      with Not_found ->
        UNAME id

(* END CN *)


let lex_comment remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  remainder lexbuf

let lex_magic remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  ch :: remainder lexbuf

let magic_token flags start_pos end_pos chars =
  let len = List.length chars in
  if not flags.at_magic_comments || len < 2 || List.hd chars != flags.magic_comment_char then
    None
  else if List.nth chars (len - 1) != flags.magic_comment_char then (
    prerr_endline
      (Pp_errors.make_message
         (Cerb_location.point end_pos)
         Errors.(CPARSER Cparser_mismatched_magic_comment)
         Warning);
    None
  ) else (
    let str = String.init (len - 2) (List.nth (List.tl chars)) in
    let loc = Cerb_location.(region (start_pos, end_pos) NoCursor) in
    let c = List.hd chars in
    Some (CERB_MAGIC (loc, (c,str)))
  )

}

(* ========================================================================== *)

(* STD §6.4.4.1#1 *)
let digit    = ['0'-'9']

let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']

let long_long_suffix = "ll" | "LL"

let long_suffix = ['l' 'L']

let unsigned_suffix = ['u' 'U']

let integer_suffix =
    unsigned_suffix long_long_suffix
  | unsigned_suffix long_suffix?
  | long_long_suffix unsigned_suffix?
  | long_suffix unsigned_suffix?


let octal_digit = ['0'-'7']

let nonzero_digit = ['1'-'9']

let hexadecimal_prefix = "0x" | "0X"

let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

(* since C2x *)
(* TODO: we need a mechanism to signal that a C2x feature has been used *)
let binary_prefix = "0b" | "0B"

let binary_digit = "0" | "1"

let binary_constant =
  (* TODO: removing the separator for now. We need to update the functions in
  Decode.ml for things to work *)
  (* binary_prefix (binary_digit "'"?)+ *)
  binary_prefix (binary_digit)+


let octal_constant = '0' octal_digit*

let decimal_constant = nonzero_digit digit*

(* NOTE: we do the decoding in `initial' *)
let integer_constant =
    decimal_constant
  | octal_constant
  | hexadecimal_constant
  | binary_constant (* since C2x *)


(* STD §6.4.3#1 *)
let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit

let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad


(* STD §6.4.4.1#1 *)
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let identifier_nondigit =
    nondigit
  | universal_character_name

let identifier = identifier_nondigit (identifier_nondigit | digit)*

(* STD §6.4.4.2#1 *)
let floating_suffix = ['f' 'l' 'F' 'L']

let hexadecimal_digit_sequence = hexadecimal_digit+

let digit_sequence = digit+

let sign = ['-' '+']

let binary_exponent_part =
    'p' sign? digit_sequence
  | 'P' sign? digit_sequence

let hexadecimal_fractional_constant =
    hexadecimal_digit_sequence? '.' hexadecimal_digit_sequence
  | hexadecimal_digit_sequence '.'

let exponent_part =
    'e' sign? digit_sequence
  | 'E' sign? digit_sequence

let fractional_constant =
    digit_sequence? '.' digit_sequence
  | digit_sequence '.'

(* NOTE: the suffix are added in 'initial' *)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
      binary_exponent_part (*floating_suffix?*)
  | hexadecimal_prefix hexadecimal_digit_sequence
      binary_exponent_part (*floating_suffix?*)

(* NOTE: the suffix are added in 'initial' *)
let decimal_floating_constant =
    fractional_constant exponent_part? (*floating_suffix?*)
  | digit_sequence exponent_part (*floating_suffix?*)

let floating_constant =
  decimal_floating_constant | hexadecimal_floating_constant


(* STD §6.4.4.4#1 *)
let hexadecimal_escape_sequence = "\\x" hexadecimal_digit+

let octal_escape_sequence =
    '\\' octal_digit
  | '\\' octal_digit octal_digit
  | '\\' octal_digit octal_digit octal_digit

let simple_escape_sequence =
    "\\'" | "\\\"" | "\\?" | "\\\\" | "\\a" | "\\b" | "\\f" | "\\n"
  | "\\r" | "\\t" | "\\v"

let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name

let c_char =
    [^ '\'' '\\' '\n']
  | escape_sequence

let character_constant = c_char+


(* STD §6.4.5#1 *)
let s_char =
    [^ '"' '\\' '\n']
  | escape_sequence


(* Whitespaces *)
let whitespace_char = [' ' '\t' (*'\n'*) '\012' '\r']

let lbrack_lbrack = '[' whitespace_char* '['
(*let rbrack_rbrack = ']' whitespace_char* ']'*)

(* For CN *)
let cn_integer_width = ("8" | "16" | "32" | "64" | "128")

(* ========================================================================== *)

rule s_char_sequence = parse
  | s_char as x
      { let xs = s_char_sequence lexbuf in
        x :: xs }
  | '"'
      { [] }
  | _
      { raise (Error Errors.Cparser_invalid_string_character) }

and magic flags start_of_comment = parse
  (* End of the magic comment *)
  | "*/" {[]}
  | "/*" { raise (Error Errors.Cparser_nested_comment) }
  | eof  { lexbuf.lex_start_p <- start_of_comment;
           raise (Error (Errors.Cparser_unterminated_comment (Printf.sprintf "/*%c" flags.magic_comment_char))) }
  | _    {lex_magic (magic flags start_of_comment) lexbuf}

(* Consume a comment: /* ... */ *)
(* STD §6.4.9#1 *)
and comment start_of_comment = parse
  (* End of the comment *)
  | "*/" {()}
  | "/*" { raise (Error Errors.Cparser_nested_comment) }
  | eof  { lexbuf.lex_start_p <- start_of_comment;
           raise (Error (Errors.Cparser_unterminated_comment "/*")) }
  | _    {lex_comment (comment start_of_comment) lexbuf}


(* Consume a singleline comment: // ... *)
(* STD §6.4.9#2 *)
and onelinecomment = parse
  | '\n' | eof {()}
  | _          {lex_comment onelinecomment lexbuf}


(* We assume gcc -E syntax. **)
and hash = parse
  | (' ' (('0' | decimal_constant) as n) " \""
    ([^ '\012' '\t' '"']* as file) "\"" [^ '\n']* ('\n' | eof))
      { (
        let n =
          try int_of_string n
          with Failure _ ->
            raise (Error (Errors.Cparser_invalid_line_number n))
        in
        offset_location lexbuf file n
      )}
  | ("pragma" [^ '\n']* '\n')
      { }
  | [^ '\n']* eof
      { raise (Error Errors.Cparser_unexpected_eof) }
  | _
      { raise (Error Errors.Cparser_invalid_symbol) }

(* Entry point *)
and initial flags = parse
  (* Magic comments *)
  | "/*@" { let curr_p = lexbuf.lex_curr_p in
            let xs = magic flags lexbuf.lex_start_p lexbuf in
            match magic_token flags curr_p lexbuf.lex_start_p ('@' :: xs) with
            | Some tok -> tok
            | None -> initial flags lexbuf
            }
  (* Alternative magic comments *)
  | "/*$" { let curr_p = lexbuf.lex_curr_p in
            let xs = magic flags lexbuf.lex_start_p lexbuf in
            match magic_token flags curr_p lexbuf.lex_start_p ('$' :: xs) with
            | Some tok -> tok
            | None -> initial flags lexbuf
            }
  (* Beginning of a comment *)
  | "/*" { ignore (comment lexbuf.lex_start_p lexbuf); initial flags lexbuf}

  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in new_line lexbuf; initial flags lexbuf}

  | '\n'             { new_line lexbuf; initial flags lexbuf }
  | whitespace_char+ { initial flags lexbuf }
  | '#'              { hash lexbuf; initial flags lexbuf }

  (* NOTE: we decode integer constants here *)
  | (integer_constant as str) unsigned_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_U)) }
  | (integer_constant as str) unsigned_suffix long_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_UL)) }
  | (integer_constant as str) unsigned_suffix long_long_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_ULL)) }
  | (integer_constant as str) long_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_L)) }
  | (integer_constant as str) long_long_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_LL)) }
  | (integer_constant as str) long_suffix unsigned_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_UL)) }
  | (integer_constant as str) long_long_suffix unsigned_suffix
      { CONSTANT (Cabs.CabsInteger_const (str, Some Cabs.CabsSuffix_ULL)) }
    (* For CN. Copying and adjusting Kayvan's code from above. *)
  | (integer_constant as str) 'u' (cn_integer_width as n)
      { CN_CONSTANT (str, `U, int_of_string n) }
  | (integer_constant as str) 'i' (cn_integer_width as n)
      { CN_CONSTANT (str, `I, int_of_string n) }
    (* /For CN. *)
  | (integer_constant as str)
      { CONSTANT (Cabs.CabsInteger_const (str, None)) }

  | (floating_constant as str) ('f' | 'F')
      { CONSTANT (Cabs.CabsFloating_const (str, Some Cabs.CabsFloatingSuffix_F)) }
  | (floating_constant as str) ('l' | 'L')
      { CONSTANT (Cabs.CabsFloating_const (str, Some Cabs.CabsFloatingSuffix_L)) }
  | (floating_constant as str)
      { CONSTANT (Cabs.CabsFloating_const (str, None)) }

  (* NOTE: we decode character constants here *)
  | "'" (character_constant as str) "'"
      { CONSTANT (Cabs.CabsCharacter_const (None, str)) }
  | "L'" (character_constant as str) "'"
      { CONSTANT (Cabs.CabsCharacter_const (Some Cabs.CabsPrefix_L, str)) }
  | "u'" (character_constant as str) "'"
      { CONSTANT (Cabs.CabsCharacter_const (Some Cabs.CabsPrefix_u, str)) }
  | "U'" (character_constant as str) "'"
      { CONSTANT (Cabs.CabsCharacter_const (Some Cabs.CabsPrefix_U, str)) }

  (* NOTE: we partialy (TODO) decode string literals here *)
  | '"'
      { let saved_start_p = lexbuf.lex_start_p in
        let strs = s_char_sequence lexbuf in
        lexbuf.lex_start_p <- saved_start_p;
        STRING_LITERAL (None, strs) }
  | ("u8" | 'u' | 'U' | 'L') as pref '"'
      { let pref = match pref with
          | "u8" -> Cabs.CabsEncPrefix_u8
          | "u"  -> Cabs.CabsEncPrefix_u
          | "U"  -> Cabs.CabsEncPrefix_U
          | "L"  -> Cabs.CabsEncPrefix_L
          | _    -> assert false in
        let saved_start_p = lexbuf.lex_start_p in
        let strs = s_char_sequence lexbuf in
        lexbuf.lex_start_p <- saved_start_p;
        STRING_LITERAL (Some pref, strs) }

  (* STD §6.4.6#1 Punctuators *)
  | '['   { LBRACK              }
  | ']'   { RBRACK              }
  | '('   { LPAREN              }
  | ')'   { RPAREN              }
  | '{'   { LBRACE              }
  | '}'   { RBRACE              }
  | '.'   { DOT                 }
  | "->"  { MINUS_GT            }
  | "++"  { PLUS_PLUS           }
  | "--"  { MINUS_MINUS         }
  | '&'   { AMPERSAND           }
  | '*'   { STAR                }
  | '+'   { PLUS                }
  | '-'   { MINUS               }
  | '~'   { TILDE               }
  | '!'   { BANG                }
  | '/'   { SLASH               }
  | '%'   { PERCENT             }
  | "<<"  { LT_LT               }
  | ">>"  { GT_GT               }
  | '<'   { LT                  }
  | '>'   { GT                  }
  | "<="  { LT_EQ               }
  | ">="  { GT_EQ               }
  | "=="  { EQ_EQ               }
  | "!="  { BANG_EQ             }
  | '^'   { CARET               }
  | '|'   { PIPE                }
  | "&&"  { AMPERSAND_AMPERSAND }
  | "||"  { PIPE_PIPE           }
  | '?'   { QUESTION            }
  | "::"  { COLON_COLON         }
  | ':'   { COLON               }
  | ';'   { SEMICOLON           }
  | "..." { ELLIPSIS            }
  | '='   { EQ                  }
  | "*="  { STAR_EQ             }
  | "/="  { SLASH_EQ            }
  | "%="  { PERCENT_EQ          }
  | "+="  { PLUS_EQ             }
  | "-="  { MINUS_EQ            }
  | "<<=" { LT_LT_EQ            }
  | ">>=" { GT_GT_EQ            }
  | "&="  { AMPERSAND_EQ        }
  | "^="  { CARET_EQ            }
  | "|="  { PIPE_EQ             }
  | ','   { COMMA               }
  | lbrack_lbrack { LBRACK_LBRACK }
(*  | rbrack_rbrack { RBRACK_RBRACK } *)
(*  | '#'  *)
(*  | "##" *)

  (* STD §6.4.6#3 *)
  | "<:" { LBRACK }
  | ":>" { RBRACK }
  | "<%" { LBRACE }
  | "%>" { RBRACE }
(*  | "%:"   *)
(*  | "%:%:" *)

  (* NON-STD GNU extensions *)
  | "?:" { QUESTION_COLON }

  (* NON-STD (cppmem-like thread syntax) *)
  | "{-{" { LBRACES }
  | "|||" { PIPES   }
  | "}-}" { RBRACES }

    (* copied over from backend/cn/assertion_lexer.mll *)
  | ['A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as id
      {
        if flags.inside_cn then
          cn_lex_keyword id lexbuf.lex_start_p lexbuf.lex_curr_p  
        else
          UNAME id
      }

  | identifier as id
    { try
        Hashtbl.find lexicon id
      with Not_found ->
        if flags.inside_cn then
          cn_lex_keyword id lexbuf.lex_start_p lexbuf.lex_curr_p 
        else
          LNAME id
    }
  | eof
      { EOF }
  | _
      { raise (Error Errors.Cparser_invalid_symbol) }

(* ========================================================================== *)

{
type lexer_state =
  | LSRegular
  | LSIdentifier of string


let create_lexer ~(inside_cn:bool) : [ `LEXER of lexbuf -> token ] =
  let lexer_state = ref LSRegular in
  `LEXER (fun lexbuf ->
  match !lexer_state with
  | LSRegular ->
      let at_magic_comments = Switches.(has_switch SW_at_magic_comments) in
      let magic_comment_char = 
        if Switches.(has_switch SW_magic_comment_char_dollar)
        then '$'
        else '@'
      in
      begin match initial { inside_cn; at_magic_comments; magic_comment_char } lexbuf with
      | LNAME i as tok -> lexer_state := LSIdentifier i; tok
      | UNAME i as tok -> lexer_state := LSIdentifier i; tok
      | _      as tok -> lexer_state := LSRegular; tok
      end
  | LSIdentifier i ->
      lexer_state := LSRegular;
      if Lexer_feedback.is_typedefname i then TYPE else VARIABLE)
}
