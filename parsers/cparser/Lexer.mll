{
open Lexing
open Pre_parser
open Pre_parser_aux
open Cabs0helper

module SMap = Map.Make(String)

let contexts : string list list ref = ref []
let lexicon : (string, Cabs0.cabsloc -> token) Hashtbl.t = Hashtbl.create 0

let init filename channel : Lexing.lexbuf =
  assert (!contexts = []);
  Hashtbl.clear lexicon;
  List.iter 
    (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [ ("auto", fun loc -> AUTO loc);
      ("break", fun loc -> BREAK loc);
      ("case", fun loc -> CASE loc);
      ("char", fun loc -> CHAR loc);
      ("const", fun loc -> CONST loc);
      ("continue", fun loc -> CONTINUE loc);
      ("default", fun loc -> DEFAULT loc);
      ("do", fun loc -> DO loc);
      ("double", fun loc -> DOUBLE loc);
      ("else", fun loc -> ELSE loc);
      ("enum", fun loc -> ENUM loc);
      ("extern", fun loc -> EXTERN loc);
      ("float", fun loc -> FLOAT loc);
      ("for", fun loc -> FOR loc);
      ("goto", fun loc -> GOTO loc);
      ("if", fun loc -> IF loc);
      ("inline", fun loc -> INLINE loc);
      ("int", fun loc -> INT loc);
      ("long", fun loc -> LONG loc);
      ("offsetof", fun loc -> OFFSETOF loc);
      ("register", fun loc -> REGISTER loc);
      ("restrict", fun loc -> RESTRICT loc);
      ("return", fun loc -> RETURN loc);
      ("short", fun loc -> SHORT loc);
      ("signed", fun loc -> SIGNED loc);
      ("sizeof", fun loc -> SIZEOF loc);
      ("static", fun loc -> STATIC loc);
      ("struct", fun loc -> STRUCT loc);
      ("switch", fun loc -> SWITCH loc);
      ("typedef", fun loc -> TYPEDEF loc);
      ("union", fun loc -> UNION loc);
      ("unsigned", fun loc -> UNSIGNED loc);
      ("void", fun loc -> VOID loc);
      ("volatile", fun loc -> VOLATILE loc);
      ("while", fun loc -> WHILE loc);
      ("_Alignof", fun loc -> ALIGNOF loc);
      ("_Bool", fun loc -> BOOL loc);
      ("_Thread_local", fun loc -> THREAD_LOCAL loc);
      ("_Atomic", fun loc -> ATOMIC loc);
      
      ("__c11_atomic_init", fun loc -> C11_ATOMIC_INIT loc);
      ("__c11_atomic_store", fun loc -> C11_ATOMIC_STORE loc);
      ("__c11_atomic_load", fun loc -> C11_ATOMIC_LOAD loc);
      ("__c11_atomic_exchange", fun loc -> C11_ATOMIC_EXCHANGE loc);
      ("__c11_atomic_compare_exchange_strong", fun loc -> C11_ATOMIC_COMPARE_EXCHANGE_STRONG loc);
      ("__c11_atomic_compare_exchange_weak", fun loc -> C11_ATOMIC_COMPARE_EXCHANGE_WEAK loc);
      ("__c11_atomic_fetch_key", fun loc -> C11_ATOMIC_FETCH_KEY loc);
      
      ("__builtin_va_arg", fun loc -> BUILTIN_VA_ARG loc);
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

  !declare_typename "__builtin_va_list";
  
  !declare_typename "size_t";
  !declare_typename "intptr_t";
  
  !declare_varname "assert";
  !declare_varname "NULL";
  !declare_varname "ULONG_MAX";
  
  
  
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
    unsigned_suffix long_suffix? 
  | unsigned_suffix long_long_suffix 
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

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
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED), currentLoc lexbuf) }
  | (integer_constant as s) unsigned_suffix long_suffix
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG), currentLoc lexbuf) }
  | (integer_constant as s) unsigned_suffix long_long_suffix
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG_LONG), currentLoc lexbuf) }
  | (integer_constant as s) long_suffix
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_LONG), currentLoc lexbuf) }
  | (integer_constant as s) long_suffix unsigned_suffix
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG), currentLoc lexbuf) }
  | (integer_constant as s) long_long_suffix unsigned_suffix
      { CONSTANT (Cabs0.CONST_INT (s, Some Cabs0.SUFFIX_UNSIGNED_LONG_LONG), currentLoc lexbuf) }
  | (integer_constant as s)
      { CONSTANT (Cabs0.CONST_INT (s, None), currentLoc lexbuf) }
  
  | floating_constant as s        { CONSTANT (Cabs0.CONST_FLOAT s,
                                              currentLoc lexbuf) }


  |     "'" (character_constant as s) "'"
      { CONSTANT (Cabs0.CONST_CHAR (None, s), currentLoc lexbuf) }
  | "L'" (character_constant as s) "'"
      { CONSTANT (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_L, s), currentLoc lexbuf) }
  | "u'" (character_constant as s) "'"
      { CONSTANT (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_u, s), currentLoc lexbuf) }
  | "U'" (character_constant as s) "'"
      { CONSTANT (Cabs0.CONST_CHAR (Some Cabs0.PREFIX_U, s), currentLoc lexbuf) }


  | string_literal as s           { STRING_LITERAL (s, currentLoc lexbuf) }
  | "..."                         { ELLIPSIS(currentLoc lexbuf) }
  | "+="                          { ADD_ASSIGN(currentLoc lexbuf) }
  | "-="                          { SUB_ASSIGN(currentLoc lexbuf) }
  | "*="                          { MUL_ASSIGN(currentLoc lexbuf) }
  | "/="                          { DIV_ASSIGN(currentLoc lexbuf) }
  | "%="                          { MOD_ASSIGN(currentLoc lexbuf) }
  | "|="                          { OR_ASSIGN(currentLoc lexbuf) }
  | "&="                          { AND_ASSIGN(currentLoc lexbuf) }
  | "^="                          { XOR_ASSIGN(currentLoc lexbuf) }
  | "<<="                         { LEFT_ASSIGN(currentLoc lexbuf) }
  | ">>="                         { RIGHT_ASSIGN(currentLoc lexbuf) }
  | "<<"                          { LEFT(currentLoc lexbuf) }
  | ">>"                          { RIGHT(currentLoc lexbuf) }
  | "=="                          { EQEQ(currentLoc lexbuf) }
  | "!="                          { NEQ(currentLoc lexbuf) }
  | "<="                          { LEQ(currentLoc lexbuf) }
  | ">="                          { GEQ(currentLoc lexbuf) }
  | "="                           { EQ(currentLoc lexbuf) }
  | "<"                           { LT(currentLoc lexbuf) }
  | ">"                           { GT(currentLoc lexbuf) }
  | "++"                          { INC(currentLoc lexbuf) }
  | "--"                          { DEC(currentLoc lexbuf) }
  | "->"                          { PTR(currentLoc lexbuf) }
  | "+"                           { PLUS(currentLoc lexbuf) }
  | "-"                           { MINUS(currentLoc lexbuf) }
  | "*"                           { STAR(currentLoc lexbuf) }
  | "/"                           { SLASH(currentLoc lexbuf) }
  | "%"                           { PERCENT(currentLoc lexbuf) }
  | "!"                           { BANG(currentLoc lexbuf) }
  | "&&"                          { ANDAND(currentLoc lexbuf) }
  | "||"                          { BARBAR(currentLoc lexbuf) }
  | "&"                           { AND(currentLoc lexbuf) }
  | "|"                           { BAR(currentLoc lexbuf) }
  | "^"                           { HAT(currentLoc lexbuf) }
  | "?"                           { QUESTION(currentLoc lexbuf) }
  | ":"                           { COLON(currentLoc lexbuf) }
  | "~"                           { TILDE(currentLoc lexbuf) }
  | "{"|"<%"                      { LBRACE(currentLoc lexbuf) }
  | "}"|"%>"                      { RBRACE(currentLoc lexbuf) }
  | "["|"<:"                      { LBRACK(currentLoc lexbuf) }
  | "]"|":>"                      { RBRACK(currentLoc lexbuf) }
  | "("                           { LPAREN(currentLoc lexbuf) }
  | ")"                           { RPAREN(currentLoc lexbuf) }
  | ";"                           { SEMICOLON(currentLoc lexbuf) }
  | ","                           { COMMA(currentLoc lexbuf) }
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
            UNKNOWN_NAME(id, ref OtherId, currentLoc lexbuf) }
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
  open Streams
  open Specif
  open Parser
  open Aut.GramDefs

  let tokens_stream lexbuf : token coq_Stream =
    let tokens = ref [] in
    let lexer_wraper lexbuf : Pre_parser.token =
      let res = initial lexbuf in
      tokens := res::!tokens;
      res
    in
    Pre_parser.translation_unit_file lexer_wraper lexbuf;
    let rec compute_token_stream accu = 
      let loop q t v =
        compute_token_stream
          (lazy (Cons (Coq_existT (t, Obj.magic v), accu)))
          q
      in 
      function
      | [] -> accu
      | t::q ->
          match t with
            | ADD_ASSIGN loc -> loop q ADD_ASSIGN_t loc
            | ALIGNOF loc -> loop q ALIGNOF_t loc
            | AND loc -> loop q AND_t loc
            | ANDAND loc -> loop q ANDAND_t loc
            | AND_ASSIGN loc -> loop q AND_ASSIGN_t loc
            | AUTO loc -> loop q AUTO_t loc
            | BANG loc -> loop q BANG_t loc
            | BAR loc -> loop q BAR_t loc
            | BARBAR loc -> loop q BARBAR_t loc
            | BOOL loc -> loop q BOOL_t loc
            | BREAK loc -> loop q BREAK_t loc
            | BUILTIN_VA_ARG loc -> loop q BUILTIN_VA_ARG_t loc
            | CASE loc -> loop q CASE_t loc
            | CHAR loc -> loop q CHAR_t loc
            | COLON loc -> loop q COLON_t loc
            | COMMA loc -> loop q COMMA_t loc
            | CONST loc -> loop q CONST_t loc
            | CONSTANT (cst, loc) -> loop q CONSTANT_t (cst, loc)
            | CONTINUE loc -> loop q CONTINUE_t loc
            | DEC loc -> loop q DEC_t loc
            | DEFAULT loc -> loop q DEFAULT_t loc
            | DIV_ASSIGN loc -> loop q DIV_ASSIGN_t loc
            | DO loc -> loop q DO_t loc
            | DOT loc -> loop q DOT_t loc
            | DOUBLE loc -> loop q DOUBLE_t loc
            | ELLIPSIS loc -> loop q ELLIPSIS_t loc
            | ELSE loc -> loop q ELSE_t loc
            | ENUM loc -> loop q ENUM_t loc
            | EOF -> loop q EOF_t ()
            | EQ loc -> loop q EQ_t loc
            | EQEQ loc -> loop q EQEQ_t loc
            | EXTERN loc -> loop q EXTERN_t loc
            | FLOAT loc -> loop q FLOAT_t loc
            | FOR loc -> loop q FOR_t loc
            | GEQ loc -> loop q GEQ_t loc
            | GOTO loc -> loop q GOTO_t loc
            | GT loc -> loop q GT_t loc
            | HAT loc -> loop q HAT_t loc
            | IF loc -> loop q IF_t loc
            | INC loc -> loop q INC_t loc
            | INLINE loc -> loop q INLINE_t loc
            | INT loc -> loop q INT_t loc
            | LBRACE loc -> loop q LBRACE_t loc
            | LBRACES loc -> loop q LBRACES_t loc
            | BARES loc -> loop q BARES_t loc
            | RBRACES loc -> loop q RBRACES_t loc
            | LBRACK loc -> loop q LBRACK_t loc
            | LEFT loc -> loop q LEFT_t loc
            | LEFT_ASSIGN loc -> loop q LEFT_ASSIGN_t loc
            | LEQ loc -> loop q LEQ_t loc
            | LONG loc -> loop q LONG_t loc
            | LPAREN loc -> loop q LPAREN_t loc
            | LT loc -> loop q LT_t loc
            | MINUS loc -> loop q MINUS_t loc
            | MOD_ASSIGN loc -> loop q MOD_ASSIGN_t loc
            | MUL_ASSIGN loc -> loop q MUL_ASSIGN_t loc
            | NEQ loc -> loop q NEQ_t loc
            | OR_ASSIGN loc -> loop q OR_ASSIGN_t loc
            | PERCENT loc -> loop q PERCENT_t loc
            | PLUS loc -> loop q PLUS_t loc
            | PTR loc -> loop q PTR_t loc
            | QUESTION loc -> loop q QUESTION_t loc
            | OFFSETOF loc -> loop q OFFSETOF_t loc
            | RBRACE loc -> loop q RBRACE_t loc
            | RBRACK loc -> loop q RBRACK_t loc
            | REGISTER loc -> loop q REGISTER_t loc
            | RESTRICT loc -> loop q RESTRICT_t loc
            | RETURN loc -> loop q RETURN_t loc
            | RIGHT loc -> loop q RIGHT_t loc
            | RIGHT_ASSIGN loc -> loop q RIGHT_ASSIGN_t loc
            | RPAREN loc -> loop q RPAREN_t loc
            | SEMICOLON loc -> loop q SEMICOLON_t loc
            | SHORT loc -> loop q SHORT_t loc
            | SIGNED loc -> loop q SIGNED_t loc
            | SIZEOF loc -> loop q SIZEOF_t loc
            | SLASH loc -> loop q SLASH_t loc
            | STAR loc -> loop q STAR_t loc
            | STATIC loc -> loop q STATIC_t loc
(*            | STATIC_ASSERT loc -> loop q STATIC_ASSERT_t loc *)
            | STRING_LITERAL (str, loc) -> 
                (* Merge consecutive string literals *)
                let rec doConcat accu = function
                  | STRING_LITERAL (str, loc)::q ->
                      doConcat (str^accu) q
                  | l -> loop l CONSTANT_t (Cabs0.CONST_STRING accu, loc)
                in
                doConcat "" (t::q)
            | STRUCT loc -> loop q STRUCT_t loc
            | SUB_ASSIGN loc -> loop q SUB_ASSIGN_t loc
            | SWITCH loc -> loop q SWITCH_t loc
            | TILDE loc -> loop q TILDE_t loc
            | TYPEDEF loc -> loop q TYPEDEF_t loc
            | TYPEDEF_NAME (id, typ, loc) 
            | UNKNOWN_NAME (id, typ, loc)
            | VAR_NAME (id, typ, loc) ->
                let terminal = match !typ with
                  | VarId -> VAR_NAME_t
                  | TypedefId -> TYPEDEF_NAME_t
                  | OtherId -> OTHER_NAME_t
                in
                loop q terminal (id, loc)
            | UNION loc -> loop q UNION_t loc
            | UNSIGNED loc -> loop q UNSIGNED_t loc
            | VOID loc -> loop q VOID_t loc
            | VOLATILE loc -> loop q VOLATILE_t loc
            | WHILE loc -> loop q WHILE_t loc
            | XOR_ASSIGN loc -> loop q XOR_ASSIGN_t loc
            | THREAD_LOCAL loc -> loop q THREAD_LOCAL_t loc
            | ATOMIC loc -> loop q ATOMIC_t loc
            
            | C11_ATOMIC_INIT loc -> loop q C11_ATOMIC_INIT_t loc
            | C11_ATOMIC_STORE loc -> loop q C11_ATOMIC_STORE_t loc
            | C11_ATOMIC_LOAD loc -> loop q C11_ATOMIC_LOAD_t loc
            | C11_ATOMIC_EXCHANGE loc -> loop q C11_ATOMIC_EXCHANGE_t loc
            | C11_ATOMIC_COMPARE_EXCHANGE_STRONG loc -> loop q C11_ATOMIC_COMPARE_EXCHANGE_STRONG_t loc
            | C11_ATOMIC_COMPARE_EXCHANGE_WEAK loc -> loop q C11_ATOMIC_COMPARE_EXCHANGE_WEAK_t loc
            | C11_ATOMIC_FETCH_KEY loc -> loop q C11_ATOMIC_FETCH_KEY_t loc
    in
    compute_token_stream (lazy (assert false)) !tokens

}
