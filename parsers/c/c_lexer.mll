{
open Cerb_frontend

open Lexing
open Tokens

exception Error of Errors.cparsing_cause

type env = {
  lexicon : (string, token) Hashtbl.t;
  magic_comment_char : char; (* The character after a comment indicating to
                              * start a CN comment *)
  magic_comments : bool; (* Should we process CN comments (true) or treat them
                          * as normal comments (false) *)
}

(* WARNING: GLOBAL STATE
We wouldn't need this if the Lexing.position type was parameterized on the
type of locations or if there was some way to extend the lexer buffer with
additional user state, but I can't seem to find a way to do either of these,
so for the time being we use a global variable.

Note that one needs to call `init` when starting to work a
new (preprocessed) file.
*)
module LineMap = struct

  (** Maps a line in the preprocessed file to a filename and a line number.
  The following lines in the preprocessed file reside at the specified source
  location, until the next entry in the map. *)
  let mapping = ref (Cerb_position.LineMap.empty "")

  (** Clear all line mapping entries *)
  let init file = mapping := Cerb_position.LineMap.empty file

  (** Add a new line mapping *)
  let add line info = mapping := Cerb_position.LineMap.add line info !mapping

  (** Get the current mapping *)
  let get () = !mapping

  (** Make a position from a Lexing.position, consulting the line map *)
  let position x =
    let p1 = Cerb_position.from_lexing x in
    let line_map = !mapping in
    let src_loc = Cerb_position.LineMap.lookup (Cerb_position.line p1) line_map in
    Cerb_position.set_source src_loc p1

end



(* This is called when we we see a note from the pre-processor that
we should change the file/line number (e.g., because of #include start/end) *)
let offset_location lexbuf pos_fname pos_lnum =
  if pos_lnum > 0 then begin
    LineMap.add lexbuf.lex_curr_p.pos_lnum (pos_fname, pos_lnum)
  end;
  new_line lexbuf
  

(* STD §6.4.1#1 *)
let c11_keywords: (string * Tokens.token) list =
  [ "auto"           , AUTO
  ; "break"          , BREAK
  ; "case"           , CASE
  ; "char"           , CHAR
  ; "const"          , CONST
  ; "continue"       , CONTINUE
  ; "default"        , DEFAULT
  ; "do"             , DO
  ; "double"         , DOUBLE
  ; "else"           , ELSE
  ; "enum"           , ENUM
  ; "extern"         , EXTERN
  ; "float"          , FLOAT
  ; "for"            , FOR
  ; "goto"           , GOTO
  ; "if"             , IF
  ; "inline"         , INLINE
  ; "int"            , INT
  ; "long"           , LONG
  ; "register"       , REGISTER
  ; "restrict"       , RESTRICT
  ; "return"         , RETURN
  ; "short"          , SHORT
  ; "signed"         , SIGNED
  ; "sizeof"         , SIZEOF
  ; "static"         , STATIC
  ; "struct"         , STRUCT
  ; "switch"         , SWITCH
  ; "typedef"        , TYPEDEF
  ; "union"          , UNION
  ; "unsigned"       , UNSIGNED
  ; "void"           , VOID
  ; "volatile"       , VOLATILE
  ; "while"          , WHILE
  ; "_Alignas"       , ALIGNAS
  ; "_Alignof"       , ALIGNOF
  ; "_Atomic"        , ATOMIC
  ; "_Bool"          , BOOL
  ; "_Complex"       , COMPLEX
  ; "_Generic"       , GENERIC
    (* "_Imaginary"     , IMAGINARY; *)
  ; "_Noreturn"      , NORETURN
  ; "_Static_assert" , STATIC_ASSERT
  ; "_Thread_local"  , THREAD_LOCAL ]

let gnu11_extra_keywords: (string * Tokens.token) list =
  (* alternative spelling for ISO C11 keywords *)
  [ "__alignof"    , ALIGNOF
  ; "__alignof__"  , ALIGNOF
  ; "__asm"        , ASM
  ; "__asm__"      , ASM
  ; "__complex"    , COMPLEX
  ; "__complex__"  , COMPLEX
  ; "__const"      , CONST
  ; "__const__"    , CONST
  ; "__inline"     , INLINE
  ; "__inline__"   , INLINE
  ; "__restrict"   , RESTRICT
  ; "__restrict__" , RESTRICT
  ; "__signed"     , SIGNED
  ; "__signed__"   , SIGNED
  ; "__volatile"   , VOLATILE
  ; "__volatile__" , VOLATILE
  (* GNU11 extensions *)
  ; "__auto_type"       , AUTO_TYPE
  ; "__int128"          , INT128
  ; "__label__"         , LABEL
  ; "typeof"            , TYPEOF
  ; "__typeof__"        , TYPEOF
  ; "__typeof"          , TYPEOF
  ; "__typeof_unqual__" , TYPEOF_UNQUAL
  ; "__typeof_unqual"   , TYPEOF_UNQUAL
  ; "__extension__"     , EXTENSION
  (* ; "__thread"          , GNU_THREAD *)

  ; "asm"               , ASM

  ; "__attribute__" , ATTRIBUTE
  ; "__attribute"   , ATTRIBUTE
  ; "__builtin_offsetof"           , BUILTIN_OFFSETOF
  ; "__builtin_choose_expr"        , BUILTIN_CHOOSE_EXPR
  ; "__builtin_types_compatible_p" , BUILTIN_TYPES_COMPATIBLE_P
  (* ; "__builtin_has_attribute"      , BUILTIN_HAS_ATTRIBUTE *)
  ]

let c23_extra_keywords: (string * Tokens.token) list =
  [ "alignas"       , ALIGNAS
  ; "alignof"       , ALIGNOF
  ; "bool"          , BOOL
  ; "constexpr"     , CONSTEXPR
  ; "false"         , FALSE
  ; "nullptr"       , NULLPTR
  ; "static_assert" , STATIC_ASSERT
  ; "thread_local"  , THREAD_LOCAL
  ; "true"          , TRUE
  ; "typeof"        , TYPEOF
  ; "typeof_unqual" , TYPEOF_UNQUAL
  ; "_BitInt"       , BITINT
  ; "_Decimal32"    , DECIMAL32
  ; "_Decimal64"    , DECIMAL64
  ; "_Decimal128"   , DECIMAL128 ]

let cerb_extra_keywords: (string * Tokens.token) list =
  [ "__cerb_va_start", VA_START
  ; "__cerb_va_copy", VA_COPY
  ; "__cerb_va_arg", VA_ARG
  ; "__cerb_va_end", VA_END

  ; "__cerb_printtype", PRINT_TYPE
  ; "__BMC_ASSUME", BMC_ASSUME ]

let cerb_builtins: (string * Tokens.token) list =
  [ "__builtin_assert"  , BUILTIN_ASSERT
  ; "__builtin_offsetof", BUILTIN_OFFSETOF ]


let mk_lexicon conf : (string, token) Hashtbl.t =
  let ret = Hashtbl.create 0 in
  let add (key, builder) = Hashtbl.add ret key builder in
  List.iter add c11_keywords;
  let () = match conf.Config.lexicon with
  | C11 -> ()
  | GNU11 -> List.iter add gnu11_extra_keywords
  | C23 -> List.iter add c23_extra_keywords
  | GNU23 ->
      List.iter add gnu11_extra_keywords;
      List.iter add c23_extra_keywords
  in
  if conf.cerb_keywords then
    List.iter add cerb_extra_keywords;
  if conf.cerb_builtins then
    List.iter add cerb_builtins;
  if conf.asm_keyword then
    add ("asm", ASM);
  ret

let lex_comment remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  remainder lexbuf

let lex_magic remainder lexbuf =
  let ch = lexeme_char lexbuf 0 in
  if ch = '\n' then new_line lexbuf;
  ch :: remainder lexbuf

let magic_token env start_pos end_pos chars =
  let len = List.length chars in
  if not env.magic_comments || len < 2 || List.hd chars != env.magic_comment_char then
    None
  else if List.nth chars (len - 1) != env.magic_comment_char then (
    prerr_endline
      (Pp_errors.make_message
         (Cerb_location.point (LineMap.position end_pos))
         Errors.(C_PARSING Clexer_mismatched_magic_comment)
         Warning);
    None
  ) else (
    let str = String.init (len - 2) (List.nth (List.tl chars)) in
    let loc = Cerb_location.(region (LineMap.position start_pos, LineMap.position end_pos) NoCursor) in
    let c = List.hd chars in
    Some (CERB_MAGIC (loc, (c,str)))
  )

let region_of_lexbuf lexbuf =
  let open Cerb_location in
  region
    (LineMap.position lexbuf.lex_start_p, LineMap.position lexbuf.lex_curr_p)
    NoCursor

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
      { raise (Error Errors.Clexer_invalid_string_character) }

and magic env start_of_comment = parse
  (* End of the magic comment *)
  | "*/" {[]}
  | "/*" { raise (Error Errors.Clexer_nested_comment) }
  | eof  { lexbuf.lex_start_p <- start_of_comment;
           raise (Error (Errors.Clexer_unterminated_comment (Printf.sprintf "/*%c" env.magic_comment_char))) }
  | _    {lex_magic (magic env start_of_comment) lexbuf}

(* Consume a comment: /* ... */ *)
(* STD §6.4.9#1 *)
and comment start_of_comment = parse
  (* End of the comment *)
  | "*/" {()}
  | "/*" { raise (Error Errors.Clexer_nested_comment) }
  | eof  { lexbuf.lex_start_p <- start_of_comment;
           raise (Error (Errors.Clexer_unterminated_comment "/*")) }
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
            raise (Error (Errors.Clexer_invalid_line_number n))
        in
        offset_location lexbuf file n
      )}
  | ("pragma" [^ '\n']* '\n')
      { new_line lexbuf }
  | [^ '\n']* eof
      { raise (Error Errors.Clexer_unexpected_eof) }
  | _
      { raise (Error Errors.Clexer_invalid_symbol) }

(* Entry point *)
and initial env = parse
  (* Magic comments *)
  | "/*@" { let curr_p = lexbuf.lex_curr_p in
            let xs = magic env lexbuf.lex_start_p lexbuf in
            match magic_token env curr_p lexbuf.lex_start_p ('@' :: xs) with
            | Some tok -> tok
            | None -> initial env lexbuf
            }
  (* Alternative magic comments *)
  | "/*$" { let curr_p = lexbuf.lex_curr_p in
            let xs = magic env lexbuf.lex_start_p lexbuf in
            match magic_token env curr_p lexbuf.lex_start_p ('$' :: xs) with
            | Some tok -> tok
            | None -> initial env lexbuf
            }
  (* Beginning of a comment *)
  | "/*" { ignore (comment lexbuf.lex_start_p lexbuf); initial env lexbuf}

  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in new_line lexbuf; initial env lexbuf}

  | '\n'             { new_line lexbuf; initial env lexbuf }
  | whitespace_char+ { initial env lexbuf }
  | '#'              { hash lexbuf; initial env lexbuf }

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
        STRING_LITERAL (None, [(region_of_lexbuf lexbuf, strs)]) }
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
        STRING_LITERAL (Some pref, [(region_of_lexbuf lexbuf, strs)]) }

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

  (* NON-STD (cppmem-like thread syntax) *)
  | "{-{" { LBRACES }
  | "|||" { PIPES   }
  | "}-}" { RBRACES }

  | identifier as id
    { try Hashtbl.find env.lexicon id with Not_found -> NAME id }

  | eof
      { EOF }
  | _
      { raise (Error Errors.Clexer_invalid_symbol) }

(* ========================================================================== *)

{
type lexer_state =
  | LSRegular
  | LSIdentifier of string


(* Check that the encoding prefixes of concatenated string literals are not
 * inconsistent. *)
let merge_encoding_prefixes pref_opt1 pref_opt2 =
  match pref_opt1, pref_opt2 with
  | _, None ->
      pref_opt1
  | None, _ ->
      pref_opt2
  | Some pref1, Some pref2 ->
      if pref1 = pref2 then pref_opt1 else
        raise (Error Errors.Cparser_non_standard_string_concatenation)

let create_lexer conf : [ `LEXER of lexbuf -> token ] =
  let lexer_state = ref LSRegular in
  let Config.{ magic_comments; magic_comment_char } = conf in
  let lexicon = mk_lexicon conf in
  let env = { lexicon; magic_comments; magic_comment_char } in
  let lexer lexbuf =
    match !lexer_state with
    | LSRegular ->
        begin match initial env lexbuf with
        | NAME i as tok -> lexer_state := LSIdentifier i; tok
        | _      as tok -> lexer_state := LSRegular; tok
        end
    | LSIdentifier i ->
        lexer_state := LSRegular;
        if Lexer_feedback.is_typedefname i then TYPE else VARIABLE in
  (* The token read after a sequence of string literals, with its positions. *)
  let pending = ref None in
  `LEXER (fun lexbuf ->
  match !pending with
  | Some (tok, start_p, curr_p) ->
      pending := None;
      lexbuf.lex_start_p <- start_p;
      lexbuf.lex_curr_p  <- curr_p;
      tok
  | None ->
      begin match lexer lexbuf with
      | STRING_LITERAL (pref_opt, strs) ->
          (* STD §5.1.1.2#1, translation phase 6: "Adjacent string literal
             tokens are concatenated.". This happens before the tokens are
             analysed (phase 7), so the consecutive STRING_LITERAL tokens are
             merged here into one, which keeps the location and content of
             each string literal. *)
          let start_p = lexbuf.lex_start_p in
          let rec concat pref_opt rev_strs end_p =
            match lexer lexbuf with
            | STRING_LITERAL (pref_opt', strs') ->
                concat (merge_encoding_prefixes pref_opt pref_opt')
                  (List.rev_append strs' rev_strs) lexbuf.lex_curr_p
            | tok ->
                pending := Some (tok, lexbuf.lex_start_p, lexbuf.lex_curr_p);
                lexbuf.lex_start_p <- start_p;
                lexbuf.lex_curr_p  <- end_p;
                STRING_LITERAL (pref_opt, List.rev rev_strs) in
          concat pref_opt (List.rev strs) lexbuf.lex_curr_p
      | tok ->
          tok
      end)
}
