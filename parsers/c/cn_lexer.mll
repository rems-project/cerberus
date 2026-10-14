{
open Cerb_frontend
open Cn_tokens

exception Error of Errors.cnparsing_cause

module LineMap = C_lexer.LineMap


type keyword_kind =
 | Deprecated of string (* string: what to use instead *)
 | Production
 | Experimental
 | Unimplemented

let keywords: (string * (keyword_kind * Cn_tokens.token)) list = [
    (* C types keyword *)
    "_Alignas"       , (Production, ALIGNAS);
    "_Atomic"        , (Production, ATOMIC);
    "_Bool"          , (Production, BOOL);
    "_Complex"       , (Production, COMPLEX);
    "_Noreturn"      , (Production, NORETURN);
    "_Thread_local"  , (Production, THREAD_LOCAL);
    "auto"           , (Production, AUTO);
    "char"           , (Production, CHAR);
    "const"          , (Production, CONST);
    "double"         , (Production, DOUBLE);
    "enum"           , (Production, ENUM);
    "extern"         , (Production, EXTERN);
    "float"          , (Production, FLOAT);
    "int"            , (Production, INT);
    "long"           , (Production, LONG);
    "register"       , (Production, REGISTER);
    "restrict"       , (Production, RESTRICT);
    "short"          , (Production, SHORT);
    "signed"         , (Production, SIGNED);
    "static"         , (Production, STATIC);
    "struct"         , (Production, STRUCT);
    "typedef"        , (Production, TYPEDEF);
    "union"          , (Production, UNION);
    "unsigned"       , (Production, UNSIGNED);
    "void"           , (Production, VOID);
    "volatile"       , (Production, VOLATILE);

    (* C keyword *)
    "assert"         , (Production, ASSERT);
    "default"        , (Production, DEFAULT);
    "else"           , (Production, ELSE);
    "if"             , (Production, IF);
    "inline"         , (Production, INLINE);
    "offsetof"       , (Production, OFFSETOF);
    "return"         , (Production, RETURN);
    "sizeof"         , (Production, SIZEOF);

    (* CN 'production' keywords: well-supported and suitable for general use *)
    "i8"            , (Production, BITS (`I,8));
    "i64"           , (Production, BITS (`I,64));
    "i32"           , (Production, BITS (`I,32));
    "i16"           , (Production, BITS (`I,16));
    "i128"          , (Production, BITS (`I,128));
    "u8"            , (Production, BITS (`U,8));
    "u64"           , (Production, BITS (`U,64));
    "u32"           , (Production, BITS (`U,32));
    "u16"           , (Production, BITS (`U,16));
    "u128"          , (Production, BITS (`U,128));
    "accesses"      , (Production, ACCESSES);
    "alloc_id"      , (Production, ALLOC_ID);
    "apply"         , (Production, APPLY);
    "array_shift"   , (Production, ARRAY_SHIFT);
    "Block"         , (Deprecated "W", W);
    "boolean"       , (Production, BOOLEAN);
    "datatype"      , (Production, DATATYPE);
    "each"          , (Production, EACH);
    "ensures"       , (Production, ENSURES);
    "extract"       , (Deprecated "focus", FOCUS);
    "false"         , (Production, FALSE);
    "focus"         , (Production, FOCUS);
    "function"      , (Production, FUNCTION);
    "good"          , (Production, GOOD);
    "implies"       , (Production, IMPLIES);
    "instantiate"   , (Production, INSTANTIATE);
    "integer"       , (Production, INTEGER);
    "inv"           , (Production, INV);
    "lemma"         , (Production, LEMMA);
    "let"           , (Production, LET);
    "map"           , (Production, MAP);
    "match"         , (Production, MATCH);
    "member_shift"  , (Production, MEMBER_SHIFT);
    "NULL"          , (Production, NULL);
    "Owned"         , (Deprecated "RW", RW);
    "pointer"       , (Production, POINTER);
    "predicate"     , (Production, PREDICATE);
    "real"          , (Production, REAL);
    "requires"      , (Production, REQUIRES);
    "RW"            , (Production, RW);
    "spec"          , (Production, SPEC);
    "split_case"    , (Production, SPLIT_CASE);
    "take"          , (Production, TAKE);
    "true"          , (Production, TRUE);
    "trusted"       , (Production, TRUSTED);
    "type_synonym"  , (Production, TYPE_SYNONYM);
    "unchanged"     , (Production, UNCHANGED);
    "unfold"        , (Production, UNFOLD);
    "W"             , (Production, W);

    (* CN 'experimental' keywords - functional in some cases but not
     * recommended for general use *)
    "cn_function"   , (Experimental, CN_FUNCTION);
    "cn_ghost"      , (Experimental, CN_GHOST);
    "cn_have"       , (Experimental, CN_HAVE);
    "cn_list"       , (Experimental, CN_LIST);
    "cn_print"      , (Experimental, CN_PRINT);
    "cn_set"        , (Experimental, CN_SET);
    "cn_tuple"      , (Experimental, CN_TUPLE);
    "from_bytes"    , (Experimental, FROM_BYTES);
    "to_bytes"      , (Experimental, TO_BYTES);

    (* CN 'unimplemented' keywords - non-functional, but the keyword is
     * reserved *)
    "derive_constraints", (Production, DERIVE_CONSTRAINTS);
    "pack"              , (Unimplemented, PACK);
    "unpack"            , (Production, UNPACK);
  ]


(* This table is mutated during lexing to reduce the number of warnings
   for experimental features. Unfortunately, this makes it so that the
   behaviour of the lexer implicitly changes across multiple calls
   to [create_lexer].

   In some sense, this is fine, since Cerberus/CN only processes one
   translation unit per invocation from the command line, and we would
   likely want warnings to only occur once per invocation.

   However, if this were to change, and especially if this were to be
   made concurrent, this would need to be revisited.

   It is possible to thread the seen experimental tokens back to the caller for
   them to decide; it is also ugly. *)
let keywords =
  let table = Hashtbl.create 0 in
  List.iter (fun (key, builder) -> Hashtbl.add table key builder) keywords;
  table

(* Attempt to lex a CN keyword. These may be:
  * 'production' - well-supported and suitable for general use
  * 'experimental' - functional in some cases but not recommended for general use
  * 'unimplemented' - non-functional, but the keyword is reserved

May raise `Not_found`, indicating `id` is not a recognized CN keyword. *)
let lex_keyword id start_pos end_pos =
  (* Try to lex CN production keywords *)
  match Hashtbl.find keywords id with
  | (Production, kw) -> kw
  | (Experimental, kw) ->
    (* Only want to warn once _per CN/Cerberus invocation_ *)
    Hashtbl.replace keywords id (Production, kw);
    prerr_endline
      (Pp_errors.make_message
        Cerb_location.(region
          (LineMap.position start_pos, LineMap.position end_pos) NoCursor)
        Errors.(CN_PARSING (Cnlexer_experimental_keyword id))
        Warning);
    kw
  | (Deprecated instead, kw) ->
    (* Only want to warn once _per CN/Cerberus invocation_ *)
    Hashtbl.replace keywords id (Production, kw);
    prerr_endline
      (Pp_errors.make_message
        Cerb_location.(region
          (LineMap.position start_pos, LineMap.position end_pos) NoCursor)
        Errors.(CN_PARSING (Cnlexer_deprecated_keyword (id, instead)))
        Warning);
    kw
  | (Unimplemented, _) ->
      raise (Error (Errors.Cnlexer_unimplemented_keyword id))


let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  if ch = '\n' then Lexing.new_line lexbuf;
  remainder lexbuf
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


(* Whitespaces *)
let whitespace_char = [' ' '\t' (*'\n'*) '\012' '\r']


let integer_width = ("8" | "16" | "32" | "64" | "128")

(* ========================================================================== *)

(* Consume a comment: /* ... */ *)
(* STD §6.4.9#1 *)
rule comment start_of_comment = parse
  (* End of the comment *)
  | "*/" {()}
  | "/*" { raise (Error Errors.Cnlexer_nested_comment) }
  | eof  { lexbuf.lex_start_p <- start_of_comment;
           raise (Error (Errors.Cnlexer_unterminated_comment "/*")) }
  | _    {lex_comment (comment start_of_comment) lexbuf}


(* Consume a singleline comment: // ... *)
(* STD §6.4.9#2 *)
and onelinecomment = parse
  | '\n' | eof {()}
  | _          {lex_comment onelinecomment lexbuf}


(* Entry point *)
and lexer = parse
  (* Beginning of a comment *)
  | "/*" { ignore (comment lexbuf.lex_start_p lexbuf); lexer lexbuf}

  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; lexer lexbuf}

  | '\n'             { Lexing.new_line lexbuf; lexer lexbuf }
  | whitespace_char+ { lexer lexbuf }

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

  | (integer_constant as str) 'u' (integer_width as n)
      { CN_CONSTANT (str, `U, int_of_string n) }
  | (integer_constant as str) 'i' (integer_width as n)
      { CN_CONSTANT (str, `I, int_of_string n) }

  | (integer_constant as str)
      { PLAIN_INTEGER_CONSTANT (Cabs.CabsInteger_const (str, None)) }

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

  (* STD §6.4.6#1 Punctuators *)
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
  | '~'   { TILDE               }
  | '!'   { BANG                }
  | '/'   { SLASH               }
  | '%'   { PERCENT             }
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
  | ':'   { COLON               }
  | ';'   { SEMICOLON           }
  | "..." { ELLIPSIS            }
  | '='   { EQ                  }
  | ','   { COMMA               }
  | '_' { UNDERSCORE }

    (* copied over from (now extinct) backend/cn/assertion_lexer.mll *)
  | ['A'-'Z']['0'-'9' 'A'-'Z' 'a'-'z' '_']* as id
      {
        try
          lex_keyword id lexbuf.lex_start_p lexbuf.lex_curr_p
        with Not_found ->
          UNAME id
      }

  | identifier as id
    { try
        lex_keyword id lexbuf.lex_start_p lexbuf.lex_curr_p
      with Not_found ->
        LNAME id
    }

  | eof
      { EOF }
  | _
      { raise (Error Errors.Cnlexer_invalid_symbol) }

{}
