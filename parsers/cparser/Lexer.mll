{
open Lexing
open Pre_parser
open Pre_parser_aux
open Cabs0helper

module SMap = Map.Make(String)

open Tokens


let contexts : string list list ref = ref []
let lexicon : (string, Cabs0.cabsloc -> token) Hashtbl.t = Hashtbl.create 0

let init filename channel : Lexing.lexbuf =
  assert (!contexts = []);
  Hashtbl.clear lexicon;
  List.iter 
    (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [ ("auto", fun loc -> AUTO_ loc);
      ("break", fun loc -> BREAK_ loc);
      ("case", fun loc -> CASE_ loc);
      ("char", fun loc -> CHAR loc);
      ("const", fun loc -> CONST loc);
      ("continue", fun loc -> CONTINUE_ loc);
      ("default", fun loc -> DEFAULT_ loc);
      ("do", fun loc -> DO loc);
      ("double", fun loc -> DOUBLE loc);
      ("else", fun loc -> ELSE loc);
      ("enum", fun loc -> ENUM loc);
      ("extern", fun loc -> EXTERN_ loc);
      ("float", fun loc -> FLOAT loc);
      ("for", fun loc -> FOR_ loc);
      ("goto", fun loc -> GOTO_ loc);
      ("if", fun loc -> IF loc);
      ("inline", fun loc -> INLINE loc);
      ("int", fun loc -> INT loc);
      ("long", fun loc -> LONG loc);
      ("offsetof", fun loc -> OFFSETOF_ loc);
      ("register", fun loc -> REGISTER_ loc);
      ("restrict", fun loc -> RESTRICT loc);
      ("return", fun loc -> RETURN_ loc);
      ("short", fun loc -> SHORT loc);
      ("signed", fun loc -> SIGNED loc);
      ("sizeof", fun loc -> SIZEOF loc);
      ("static", fun loc -> STATIC_ loc);
      ("struct", fun loc -> STRUCT loc);
      ("switch", fun loc -> SWITCH_ loc);
      ("typedef", fun loc -> TYPEDEF_ loc);
      ("union", fun loc -> UNION loc);
      ("unsigned", fun loc -> UNSIGNED loc);
      ("void", fun loc -> VOID loc);
      ("volatile", fun loc -> VOLATILE loc);
      ("while", fun loc -> WHILE_ loc);
      ("_Alignof", fun loc -> ALIGNOF_ loc);
      ("_Bool", fun loc -> BOOL loc);
      ("_Thread_local", fun loc -> THREAD_LOCAL_ loc);
      ("_Atomic", fun loc -> ATOMIC loc);

(*      
      ("__c11_atomic_init", fun loc -> C11_ATOMIC_INIT_ loc);
      ("__c11_atomic_store", fun loc -> C11_ATOMIC_STORE_ loc);
      ("__c11_atomic_load", fun loc -> C11_ATOMIC_LOAD_ loc);
      ("__c11_atomic_exchange", fun loc -> C11_ATOMIC_EXCHANGE_ loc);
      ("__c11_atomic_compare_exchange_strong", fun loc -> C11_ATOMIC_COMPARE_EXCHANGE_STRONG_ loc);
      ("__c11_atomic_compare_exchange_weak", fun loc -> C11_ATOMIC_COMPARE_EXCHANGE_WEAK_ loc);
      ("__c11_atomic_fetch_key", fun loc -> C11_ATOMIC_FETCH_KEY_ loc);
*)
      
      ("__builtin_va_arg", fun loc -> BUILTIN_VA_ARG_ loc);
(*      ("_Static_assert", fun loc -> STATIC_ASSERT) *)
    ];

  push_context := begin fun () -> contexts := []::!contexts end;
  pop_context := begin fun () ->
    match !contexts with
      | [] -> assert false
      | t::q -> List.iter (Hashtbl.remove lexicon) t
  end;

 declare_varname := begin fun id ->
    Hashtbl.add lexicon id (fun loc -> VAR_NAME (id, ref VarId, loc));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (id::t)::q
  end;

  declare_typename := begin fun id ->
    Hashtbl.add lexicon id (fun loc -> TYPEDEF_NAME (id, ref TypedefId, loc));
    match !contexts with
      | [] -> ()
      | t::q -> contexts := (id::t)::q
  end;

(*
  !declare_typename "__builtin_va_list";
  
  !declare_typename "size_t";
  !declare_typename "intptr_t";
  
  !declare_varname "assert";
  !declare_varname "NULL";
  !declare_varname "ULONG_MAX";
*)
  
  (* Cerberus built-in types and variables *)
  List.iter (fun ty ->
    !declare_typename ty
  ) Builtins.builtin_typenames;
  
  List.iter (fun var ->
    !declare_varname var
  ) Builtins.builtin_varnames;
  
  
  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <-
    {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
  lb


let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf

}
(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

let identifier_nondigit =
    nondigit
(*| universal_character_name*)
  | '$'

let identifier = identifier_nondigit (identifier_nondigit|digit)*

(* Whitespaces *)
let whitespace_char = [' ' '\t' '\n' '\012' '\r']

(* Integer constants *)
let nonzero_digit = ['1'-'9']
let decimal_constant = nonzero_digit digit*

let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_long_suffix 
  | unsigned_suffix long_suffix?
  | long_long_suffix unsigned_suffix?
  | long_suffix unsigned_suffix?

(*
let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?
*)

(* Floating constants *)
let sign = ['-' '+']
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L']

let fractional_constant =
    digit_sequence? '.' digit_sequence
  | digit_sequence '.'
let exponent_part =
    'e' sign? digit_sequence
  | 'E' sign? digit_sequence
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | digit_sequence exponent_part floating_suffix?

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    hexadecimal_digit_sequence? '.' hexadecimal_digit_sequence
  | hexadecimal_digit_sequence '.'
let binary_exponent_part =
    'p' sign? digit_sequence
  | 'P' sign? digit_sequence
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix hexadecimal_digit_sequence
        binary_exponent_part floating_suffix?

let floating_constant =
  decimal_floating_constant | hexadecimal_floating_constant
                
(* Charater constants *)
let simple_escape_sequence =
    "\\'" | "\\\"" | "\\?" | "\\\\" | "\\a" | "\\b" | "\\f" | "\\n"
  | "\\r" | "\\t" | "\\v"
let octal_escape_sequence =
    '\\' octal_digit
  | '\\' octal_digit octal_digit
  | '\\' octal_digit octal_digit octal_digit
let hexadecimal_escape_sequence = "\\x" hexadecimal_digit+
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name
let c_char =
    [^ '\'' '\\' '\n']
  | escape_sequence
let character_constant = c_char+

(* String literals *)
let s_char =
    [^ '"' '\\' '\n']
  | escape_sequence
let s_char_sequence = s_char+
let string_literal =
    '"' s_char_sequence? '"'
  | 'L' '"' s_char_sequence? '"'

let integer_constant =
    decimal_constant
  | octal_constant
  | hexadecimal_constant

rule initial = parse
  (* Beginning of a comment *)
  | "/*" {let _ = comment lexbuf in initial lexbuf}
  
  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; initial lexbuf}
  
  
  | '\n'                          { new_line lexbuf; initial lexbuf }
  | whitespace_char               { initial lexbuf }
  | '#'                           { hash lexbuf}
  

  | (integer_constant as s) unsigned_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED), currentLoc lexbuf) }
  
  | (integer_constant as s) unsigned_suffix long_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s) unsigned_suffix long_long_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s) long_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s) long_long_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_LONG_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s) long_suffix unsigned_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s) long_long_suffix unsigned_suffix
      { CONSTANT_ (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG_LONG), currentLoc lexbuf) }
  
  | (integer_constant as s)
      { CONSTANT_ (Cabs0.CONST_INT (s, None), currentLoc lexbuf) }
  
  | floating_constant as s        { CONSTANT_ (Cabs0.CONST_FLOAT s,
                                              currentLoc lexbuf) }


  |     "'" (character_constant as s) "'"
      { CONSTANT_ (Cabs0.CONST_CHAR (None, s), currentLoc lexbuf) }
  | "L'" (character_constant as s) "'"
      { CONSTANT_ (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_L, s), currentLoc lexbuf) }
  | "u'" (character_constant as s) "'"
      { CONSTANT_ (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_u, s), currentLoc lexbuf) }
  | "U'" (character_constant as s) "'"
      { CONSTANT_ (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_U, s), currentLoc lexbuf) }


  | string_literal as s           { STRING_LITERAL (s, currentLoc lexbuf) }
  | "..."                         { ELLIPSIS(currentLoc lexbuf) }
  | "+="                          { ADD_ASSIGN_(currentLoc lexbuf) }
  | "-="                          { SUB_ASSIGN_(currentLoc lexbuf) }
  | "*="                          { MUL_ASSIGN_(currentLoc lexbuf) }
  | "/="                          { DIV_ASSIGN_(currentLoc lexbuf) }
  | "%="                          { MOD_ASSIGN_(currentLoc lexbuf) }
  | "|="                          { OR_ASSIGN(currentLoc lexbuf) }
  | "&="                          { AND_ASSIGN(currentLoc lexbuf) }
  | "^="                          { XOR_ASSIGN_(currentLoc lexbuf) }
  | "<<="                         { LEFT_ASSIGN(currentLoc lexbuf) }
  | ">>="                         { RIGHT_ASSIGN(currentLoc lexbuf) }
  | "<<"                          { LEFT(currentLoc lexbuf) }
  | ">>"                          { RIGHT(currentLoc lexbuf) }
  | "=="                          { EQEQ(currentLoc lexbuf) }
  | "!="                          { NEQ(currentLoc lexbuf) }
  | "<="                          { LEQ(currentLoc lexbuf) }
  | ">="                          { GEQ(currentLoc lexbuf) }
  | "="                           { EQ_(currentLoc lexbuf) }
  | "<"                           { LT_(currentLoc lexbuf) }
  | ">"                           { GT_(currentLoc lexbuf) }
  | "++"                          { INC(currentLoc lexbuf) }
  | "--"                          { DEC(currentLoc lexbuf) }
  | "->"                          { PTR_(currentLoc lexbuf) }
  | "+"                           { PLUS_(currentLoc lexbuf) }
  | "-"                           { MINUS_(currentLoc lexbuf) }
  | "*"                           { STAR(currentLoc lexbuf) }
  | "/"                           { SLASH(currentLoc lexbuf) }
  | "%"                           { PERCENT(currentLoc lexbuf) }
  | "!"                           { BANG(currentLoc lexbuf) }
  | "&&"                          { ANDAND(currentLoc lexbuf) }
  | "||"                          { BARBAR(currentLoc lexbuf) }
  | "&"                           { AND_(currentLoc lexbuf) }
  | "|"                           { BAR(currentLoc lexbuf) }
  | "^"                           { HAT(currentLoc lexbuf) }
  | "?"                           { QUESTION_(currentLoc lexbuf) }
  | ":"                           { COLON(currentLoc lexbuf) }
  | "~"                           { TILDE(currentLoc lexbuf) }
  | "{"|"<%"                      { LBRACE(currentLoc lexbuf) }
  | "}"|"%>"                      { RBRACE(currentLoc lexbuf) }
  | "["|"<:"                      { LBRACK(currentLoc lexbuf) }
  | "]"|":>"                      { RBRACK(currentLoc lexbuf) }
  | "("                           { LPAREN(currentLoc lexbuf) }
  | ")"                           { RPAREN(currentLoc lexbuf) }
  | ";"                           { SEMICOLON(currentLoc lexbuf) }
  | ","                           { COMMA_(currentLoc lexbuf) }
  | "."                           { DOT(currentLoc lexbuf) }
  
  | "{{{"                         { LBRACES(currentLoc lexbuf) }
  | "|||"                         { BARES(currentLoc lexbuf) }
  | "}}}"                         { RBRACES(currentLoc lexbuf) }
  
  | identifier as id              {
        try Hashtbl.find lexicon id (currentLoc lexbuf)
        with Not_found ->
          let pref = "__builtin_" in
          if String.length id > String.length pref &&
            String.sub id 0 (String.length pref) = pref then
              VAR_NAME (id, ref VarId, currentLoc lexbuf)
          else
            UNKNOWN_NAME(id, ref (OtherId "Lexer.mll"), currentLoc lexbuf) }
|		eof			{EOF}
  | _                             { 
      Parser_errors.fatal_error "%s:%d Error:@ invalid symbol"
        lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum }

(* We assume gcc -E syntax. **)
and hash = parse
  | ' ' (decimal_constant as n) " \"" ([^ '\012' '\t' '"']* as file) "\"" [^ '\n']* '\n'
      { let n =
	  try int_of_string n
	  with Failure "int_of_string" -> 
            Parser_errors.fatal_error "%s:%d Error:@ invalid line number"
              lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum
	in
	lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file; pos_lnum = n };
        initial lexbuf }
  | "pragma" [^ '\n']* '\n'
      { (* TODO *)
	 initial lexbuf }
  | [^ '\n']* eof
       { Parser_errors.fatal_error "%s:%d Error:@ unexpected end of file"
           lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum }
  | _ 
      { Parser_errors.fatal_error "%s:%d Error:@ invalid symbol"
          lexbuf.lex_curr_p.pos_fname lexbuf.lex_curr_p.pos_lnum }


(* Consume a comment: /* ... */ *)
and comment = parse
  (* End of the comment *)
  | "*/" {[]}
  | _    {lex_comment comment lexbuf}


(* Consume a singleline comment: // ... *)
and onelinecomment = parse
  | '\n' | eof {[]}
  | _          {lex_comment onelinecomment lexbuf}


{

}
