{
open Pre_parser
open Pre_parser_aux

module SMap = Map.Make(String)

open Tokens


let mk_loc lexbuf =
  (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)


let offset_location lexbuf new_file new_lnum char_offset =
  Lexing.(
    lexbuf.lex_curr_p <- {
      pos_fname = new_file;
      pos_lnum = new_lnum;
      pos_bol = lexbuf.lex_curr_p.pos_bol + char_offset;
      pos_cnum = lexbuf.lex_curr_p.pos_cnum + char_offset
    }
  )




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
(*    "_Imaginary"     , IMAGINARY; *)
    "_Noreturn"      , NORETURN;
    "_Static_assert" , STATIC_ASSERT;
    "_Thread_local"  , THREAD_LOCAL;
    
    "assert", ASSERT;
    "offsetof", OFFSETOF;
    "__cerbvar_va_start", VA_START;
    "__cerbvar_va_arg", VA_ARG;
    
    "__cerb_printtype", PRINT_TYPE;
  ]




let contexts: string list list ref =
  ref []
let lexicon: (string, token) Hashtbl.t =
  Hashtbl.create 0


(* This needs to be called before using `initial' *)
let init filename channel: Lexing.lexbuf =
  assert (!contexts = []);
  Hashtbl.clear lexicon;
  List.iter (fun (key, builder) ->
    Hashtbl.add lexicon key builder
  ) keywords;
  
  push_context := begin fun () -> contexts := [] :: !contexts end;
  pop_context  := begin fun () ->
    match !contexts with
      | [] -> assert false
      | t::q -> List.iter (Hashtbl.remove lexicon) t
  end;
  
(*
 declare_varname := begin fun (Cabs.CabsIdentifier (_, str) as id) ->
    Hashtbl.add lexicon str (VAR_NAME (id, ref VarId));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (str::t)::q
  end;
  
  declare_typename := begin fun (Cabs.CabsIdentifier (_, str) as id) ->
    Hashtbl.add lexicon str (TYPEDEF_NAME (id, ref TypedefId));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (str::t)::q
  end;
*)
 declare_varname := begin fun str ->
    Hashtbl.add lexicon str (VAR_NAME (str, ref VarId));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (str::t)::q
  end;
  
  declare_typename := begin fun str ->
    Hashtbl.add lexicon str (TYPEDEF_NAME (str, ref TypedefId));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (str::t)::q
  end;
  
  let lb = Lexing.from_channel channel in
  lb.Lexing.lex_curr_p <- {lb.Lexing.lex_curr_p with Lexing.pos_fname = filename; Lexing.pos_lnum = 1};
  lb


let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf
}


(* STD §6.4.1#1 *)
let nondigit = ['_' 'a'-'z' 'A'-'Z']
let digit    = ['0'-'9']

let identifier_nondigit =
    nondigit
(*| universal_character_name *) (* TODO *)
  | '$' (* TODO(check) NON-STD? *)

let identifier = identifier_nondigit (identifier_nondigit | digit)*


(* STD §6.4.4.1#1 *)
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']


(* STD §6.4.3#1 *)
let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit

let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad


(* STD §6.4.4.1#1 *)
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

(* (* NOTE: we instead do the decoding in `initial' *)
let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?
*)


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

let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix hexadecimal_digit_sequence
        binary_exponent_part floating_suffix?

let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | digit_sequence exponent_part floating_suffix?

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

(* let s_char_sequence = s_char+ *) (* NOTE: replaced by a rule of the same name *)

(* (* NOTE: we instead do the decoding in `initial' *)
let string_literal =
    '"' s_char_sequence? '"'
  | "u8" '"' s_char_sequence? '"'
  | 'u' '"' s_char_sequence? '"'
  | 'U' '"' s_char_sequence? '"'
  | 'L' '"' s_char_sequence? '"'
*)

let integer_constant =
    decimal_constant
  | octal_constant
  | hexadecimal_constant


(* Whitespaces *)
let whitespace_char = [' ' '\t' '\n' '\012' '\r']



















rule s_char_sequence = parse
  | s_char as x
      { let xs = s_char_sequence lexbuf in
        x :: xs }
  | '"'
      { [] }



(* Consume a comment: /* ... */ *)
and comment = parse
  (* End of the comment *)
  | "*/" {[]}
  | _    {lex_comment comment lexbuf}


(* Consume a singleline comment: // ... *)
and onelinecomment = parse
  | '\n' | eof {[]}
  | _          {lex_comment onelinecomment lexbuf}


(* We assume gcc -E syntax. **)
and hash = parse
  | (' ' (decimal_constant as n) " \"" ([^ '\012' '\t' '"']* as file) "\"" [^ '\n']* '\n') as l
      { Lexing.(
          let n =
  	    try
              int_of_string n
            with
              Failure "int_of_string" -> 
                Parser_errors.fatal_error "%s:%d Error:@ invalid line number"
                  lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum in
          offset_location lexbuf file n ((String.length l));
(*          print_endline "FOUND A HASH"; (* DEBUG *) *)
          String.length l
        )}
(*
  | "pragma" [^ '\n']* '\n'
      { (* TODO *)
	 initial lexbuf }
  | [^ '\n']* eof
       { Parser_errors.fatal_error "%s:%d Error:@ unexpected end of file"
           lexbuf.Lexing.lex_curr_p.Lexing.pos_fname lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum }
  | _ 
      { Parser_errors.fatal_error "%s:%d Error:@ invalid symbol"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum }
*)
  | ("pragma" [^ '\n']* '\n' as l)
      { String.length l }
  | [^ '\n']* eof
       { Parser_errors.fatal_error "%s:%d Error:@ unexpected end of file"
           lexbuf.Lexing.lex_curr_p.Lexing.pos_fname lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum }
  | _ 
      { Parser_errors.fatal_error "%s:%d Error:@ invalid symbol"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum }




(* Entry point *)
and initial = parse
  (* Beginning of a comment *)
  | "/*" {let _ = comment lexbuf in initial lexbuf}
  
  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; initial lexbuf}
  
  | '\n'            { Lexing.new_line lexbuf; initial lexbuf }
  | whitespace_char { initial lexbuf }
  | '#'             { 
(*
let offset = hash lexbuf in
                      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                        pos_bol = lexbuf.lex_curr_p.pos_cnum
                      };
*)
                      hash lexbuf;
(*                      Printf.printf ">>> %d\n" lexbuf.lex_curr_p.pos_bol; *)
                      initial lexbuf
                    }
  
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
  
  | floating_constant as str
      { CONSTANT (Cabs.CabsFloating_const str) }
  
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
      { let strs = s_char_sequence lexbuf in
        STRING_LITERAL (None, strs) }
  | ("u8" | 'u' | 'U' | 'L') as pref '"'
      { let pref = match pref with
          | "u8" -> Cabs.CabsEncPrefix_u8
          | "u"  -> Cabs.CabsEncPrefix_u
          | "U"  -> Cabs.CabsEncPrefix_U
          | "L"  -> Cabs.CabsEncPrefix_L  in
        let strs = s_char_sequence lexbuf in
        STRING_LITERAL (Some pref, strs) }
  
  (* STD §6.4.6#1 Punctuators *)
  | '['   { LBRACKET            }
  | ']'   { RBRACKET            }
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
(*  | '#'  *)
(*  | "##" *)
  
  (* STD §6.4.6#3 *)
  | "<:" { LBRACKET }
  | ":>" { RBRACKET }
  | "<%" { LBRACE   }
  | "%>" { RBRACE   }
(*  | "%:"   *)
(*  | "%:%:" *)

  (* NON-STD (cppmem-like thread syntax) *)
  | "{-{" { LBRACES }
  | "|||" { PIPES   }
  | "}-}" { RBRACES }
  
  
  (* STD §6.7.2.4#4, sentence 2 *)
  | "_Atomic" (' ')* "(" { ATOMIC_LPAREN }

(*
  | identifier as str
      { try
          Hashtbl.find lexicon str
        with Not_found ->
          (* KKK new lexing *)
          IDENTIFIER str
*)

  | identifier as str
      { try
          Hashtbl.find lexicon str
        with Not_found ->
          let pref_var = "__cerbvar_" in
          let pref_ty  = "__cerbty_"  in
          if    String.length str > String.length pref_ty
             && String.sub str 0 (String.length pref_ty) = pref_ty then
            TYPEDEF_NAME (str (* Cabs.CabsIdentifier (mk_loc lexbuf, str) *), ref TypedefId)
          else if    String.length str > String.length pref_var
                  && String.sub str 0 (String.length pref_var) = pref_var then
(
(*            Printf.printf "LEXER FOUND IDENTIFIER %s (VAR_NAME)\n" str; *)
            VAR_NAME (str (* Cabs.CabsIdentifier (mk_loc lexbuf, str) *), ref VarId)
)
          else
(
(*            Printf.printf "LEXER FOUND IDENTIFIER %s (UNKNOWN_NAME)\n" str; *)
            UNKNOWN_NAME(str (* Cabs.CabsIdentifier (mk_loc lexbuf, str) *), ref (OtherId "Lexer.mll"))
)
      }
  
  | eof
      { EOF }
  | _
      { Parser_errors.fatal_error "%s:%d Error:@ invalid symbol"
        lexbuf.Lexing.lex_curr_p.Lexing.pos_fname lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      }




{

}
