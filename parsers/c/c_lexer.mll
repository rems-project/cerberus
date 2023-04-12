{
open Cerb_frontend

open Lexing
open Tokens

exception Error of Errors.cparser_cause

type internal_state = {
  mutable inside_cn: bool;
  (* HACK fo fix col positions when seing CN keywords (look at C_parser_driver) *)
  mutable cnum_hack: int;
  mutable start_of_comment: Lexing.position;
  mutable ignore_magic: bool;
  mutable magic_acc: (Location_ocaml.t * string) list;
}
let internal_state = {
  inside_cn= false;
  cnum_hack= 0;
  start_of_comment= Lexing.dummy_pos;
  ignore_magic= false;
  magic_acc= [];
}

let fetch_and_clear_magic () =
  let ret = internal_state.magic_acc in
  internal_state.magic_acc <- [];
  List.rev ret

let restore_magic xs =
  internal_state.magic_acc <- List.rev xs


let new_line lexbuf =
  (* the hacked col offset MUST be reset after every newline *)
  internal_state.cnum_hack <- 0;
  Lexing.new_line lexbuf

let offset_location lexbuf pos_fname pos_lnum =
  if pos_lnum > 0 then
    let pos_lnum = pos_lnum - 1 in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname; pos_lnum};
  new_line lexbuf

(* STD §6.4.1#1 *)
let keywords: (string * (unit -> Tokens.token)) list = [
    "auto"           , (fun () -> AUTO);
    "break"          , (fun () -> BREAK (fetch_and_clear_magic ()));
    "case"           , (fun () -> CASE (fetch_and_clear_magic ()));
    "char"           , (fun () -> CHAR);
    "const"          , (fun () -> CONST);
    "continue"       , (fun () -> CONTINUE (fetch_and_clear_magic ()));
    "default"        , (fun () -> DEFAULT (fetch_and_clear_magic ()));
    "do"             , (fun () -> DO (fetch_and_clear_magic ()));
    "double"         , (fun () -> DOUBLE);
    "else"           , (fun () -> ELSE);
    "enum"           , (fun () -> ENUM);
    "extern"         , (fun () -> EXTERN);
    "float"          , (fun () -> FLOAT);
    "for"            , (fun () -> FOR (fetch_and_clear_magic ()));
    "goto"           , (fun () -> GOTO (fetch_and_clear_magic ()));
    "if"             , (fun () -> IF (fetch_and_clear_magic ()));
    "inline"         , (fun () -> INLINE);
    "int"            , (fun () -> INT);
    "long"           , (fun () -> LONG);
    "register"       , (fun () -> REGISTER);
    "restrict"       , (fun () -> RESTRICT);
    "return"         , (fun () -> RETURN (fetch_and_clear_magic ()));
    "short"          , (fun () -> SHORT);
    "signed"         , (fun () -> SIGNED);
    "sizeof"         , (fun () -> SIZEOF);
    "static"         , (fun () -> STATIC);
    "struct"         , (fun () -> STRUCT);
    "switch"         , (fun () -> SWITCH (fetch_and_clear_magic ()));
    "typedef"        , (fun () -> TYPEDEF);
    "typeof"         , (fun () -> TYPEOF);
    "union"          , (fun () -> UNION);
    "unsigned"       , (fun () -> UNSIGNED);
    "void"           , (fun () -> VOID);
    "volatile"       , (fun () -> VOLATILE);
    "while"          , (fun () -> WHILE (fetch_and_clear_magic ()));
    "_Alignas"       , (fun () -> ALIGNAS);
    "_Alignof"       , (fun () -> ALIGNOF);
    "_Atomic"        , (fun () -> ATOMIC);
    "_Bool"          , (fun () -> BOOL);
    "_Complex"       , (fun () -> COMPLEX);
    "_Generic"       , (fun () -> GENERIC);
    "_Imaginary"     , (fun () -> IMAGINARY);
    "_Noreturn"      , (fun () -> NORETURN);
    "_Static_assert" , (fun () -> STATIC_ASSERT);
    "_Thread_local"  , (fun () -> THREAD_LOCAL);

    "assert", (fun () -> ASSERT);
    "offsetof", (fun () -> OFFSETOF);
    "__cerb_va_start", (fun () -> VA_START);
    "__cerb_va_copy", (fun () -> VA_COPY);
    "__cerb_va_arg", (fun () -> VA_ARG);
    "__cerb_va_end", (fun () -> VA_END);

    "__cerb_printtype", (fun () -> PRINT_TYPE);

    "__BMC_ASSUME", (fun () -> BMC_ASSUME);

    (* some GCC extensions *)
    "asm", (fun () -> ASM);
    "__asm__", (fun () -> ASM);
    "__volatile__", (fun () -> ASM_VOLATILE);
    "__builtin_types_compatible_p", (fun () -> BUILTIN_TYPES_COMPATIBLE_P);

    (* BEGIN CN *)
    "__cerb_predicate"     , (fun () -> CN_PREDICATE);
    "__cerb_function"      , (fun () -> CN_FUNCTION);
    "__cerb_lemma"         , (fun () -> CN_LEMMA);
    "__cerb_datatype"      , (fun () -> CN_DATATYPE);
    "__cerb_pack"          , (fun () -> CN_PACK);
    "__cerb_unpack"        , (fun () -> CN_UNPACK);
    "__cerb_have"          , (fun () -> CN_HAVE);
    "__cerb_instantiate"   , (fun () -> CN_INSTANTIATE);
    (* END CN *)
  ]

let lexicon: (string, unit -> token) Hashtbl.t =
  let lexicon = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add lexicon key builder in
  List.iter add keywords; lexicon


(* BEGIN CN *)
let cn_keywords: (string * Tokens.token) list = [
    "good"          , CN_GOOD;
    "bool"          , CN_BOOL;
    "boolean"       , CN_BOOL;
    "CN_bool"       , CN_BOOL;
    "integer"       , CN_INTEGER;
    "CN_integer"    , CN_INTEGER;
    "real"          , CN_REAL;
    "pointer"       , CN_POINTER;
    "map"           , CN_MAP;
    "list"          , CN_LIST;
    "tuple"         , CN_TUPLE;
    "set"           , CN_SET;
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
    "cn_function"   , CN_FUNCTION;
    "when"          , CN_WHEN;
    "unchanged"     , CN_UNCHANGED;
    "pack"          , CN_PACK;
    "unpack"        , CN_UNPACK;
    "instantiate"   , CN_INSTANTIATE;
    "have"          , CN_HAVE;
    "unfold"        , CN_UNFOLD;
    "apply"         , CN_APPLY;
    "match"         , CN_MATCH;
  ]

let cn_lexicon: (string, token) Hashtbl.t =
  let cn_lexicon = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add cn_lexicon key builder in
  List.iter add cn_keywords; cn_lexicon
(* END CN *)


let lex_comment remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  remainder lexbuf

let lex_magic remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  ch :: remainder lexbuf
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

let octal_constant = '0' octal_digit*

let decimal_constant = nonzero_digit digit*

(* NOTE: we do the decoding in `initial' *)
let integer_constant =
    decimal_constant
  | octal_constant
  | hexadecimal_constant


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

(* ========================================================================== *)

rule s_char_sequence = parse
  | s_char as x
      { let xs = s_char_sequence lexbuf in
        x :: xs }
  | '"'
      { [] }

and magic = parse
  (* End of the magic comment *)
  | "*/" {[]}
  | "/*" { raise (Error Errors.Cparser_nested_comment) }
  | eof  { lexbuf.lex_start_p <- internal_state.start_of_comment;
           raise (Error (Errors.Cparser_unterminated_comment "/*@")) }
  | _    {lex_magic magic lexbuf}

(* Consume a comment: /* ... */ *)
(* STD §6.4.9#1 *)
and comment = parse
  (* End of the comment *)
  | "*/" {()}
  | "/*" { raise (Error Errors.Cparser_nested_comment) }
  | eof  { lexbuf.lex_start_p <- internal_state.start_of_comment;
           raise (Error (Errors.Cparser_unterminated_comment "/*")) }
  | _    {lex_comment comment lexbuf}


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
and initial = parse
  (* Magic comments *)
  | "/*@" { internal_state.start_of_comment <- lexbuf.lex_start_p;
            let xs = magic lexbuf in
            let str = String.init (List.length xs) (List.nth xs) in
            let sz = String.length str in
            (* ignoring magic comment that are not closed with a @*/ (not sure about this) *)
            begin if sz > 0 && String.(get str (sz - 1)) = '@' then
              let magik = String.sub str 0 (sz-1) in
              let loc = Location_ocaml.(region
                ( {internal_state.start_of_comment with pos_cnum = internal_state.start_of_comment.pos_cnum + 3}
                , {lexbuf.lex_curr_p with pos_cnum = lexbuf.lex_curr_p.pos_cnum - 3} ) NoCursor) in
              begin if not (internal_state.ignore_magic) then
                internal_state.magic_acc <- (loc, magik) :: internal_state.magic_acc
              end
            end;
            initial lexbuf }

  (* Beginning of a comment *)
  | "/*" { internal_state.start_of_comment <- lexbuf.lex_start_p;
           ignore (comment lexbuf); initial lexbuf}

  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in new_line lexbuf; initial lexbuf}

  | '\n'             { new_line lexbuf; initial lexbuf }
  | whitespace_char+ { initial lexbuf }
  | '#'              { hash lexbuf; initial lexbuf }

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
  | '{'   { LBRACE (fetch_and_clear_magic ()) }
  | '}'   { RBRACE (fetch_and_clear_magic ()) }
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
  | ';'   { SEMICOLON (fetch_and_clear_magic ()) }
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
  | "<%" { LBRACE (fetch_and_clear_magic ()) }
  | "%>" { RBRACE (fetch_and_clear_magic ()) }
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
        if internal_state.inside_cn then
          try Hashtbl.find cn_lexicon id
          with Not_found ->
            UNAME id
        else
          UNAME id
      }

  | identifier as id
    { try
        let mk_tok = Hashtbl.find lexicon id in
        match mk_tok () with
          | CN_FUNCTION ->
              (* let old_pos_cnum = lexbuf.lex_curr_p.pos_cnum in
              let new_pos_cnum = old_pos_cnum - (String.length "__cerb_") in
              Printf.fprintf stderr "HACK pos_cnum: %d --> %d\n"
                (old_pos_cnum - lexbuf.lex_curr_p.pos_bol) (new_pos_cnum - lexbuf.lex_curr_p.pos_bol);
              lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_cnum= new_pos_cnum }; *)
              CN_FUNCTION
          | CN_PREDICATE ->
              (* let old_pos_cnum = lexbuf.lex_curr_p.pos_cnum in
              let new_pos_cnum = old_pos_cnum - (String.length "__cerb_") in
              Printf.fprintf stderr "HACK pos_cnum: %d --> %d\n"
                (old_pos_cnum - lexbuf.lex_curr_p.pos_bol) (new_pos_cnum - lexbuf.lex_curr_p.pos_bol);
              lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_cnum= new_pos_cnum }; *)
              CN_PREDICATE
          | CN_LEMMA ->
              (* let old_pos_cnum = lexbuf.lex_curr_p.pos_cnum in
              let new_pos_cnum = old_pos_cnum - (String.length "__cerb_") in
              Printf.fprintf stderr "HACK pos_cnum: %d --> %d\n"
                (old_pos_cnum - lexbuf.lex_curr_p.pos_bol) (new_pos_cnum - lexbuf.lex_curr_p.pos_bol);
              lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_cnum= new_pos_cnum }; *)
              CN_LEMMA
          | tok ->
              tok
      with Not_found ->
        if internal_state.inside_cn then
          try Hashtbl.find cn_lexicon id
          with Not_found ->
            LNAME id
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

let lexer_state = ref LSRegular

let lexer : lexbuf -> token = fun lexbuf ->
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
