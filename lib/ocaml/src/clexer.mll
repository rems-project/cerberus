(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
(* FrontC -- lexical analyzer
**
** 1.0	3.22.99	Hugues Cassé	First version.
** 2.0  George Necula 12/12/00: Many extensions
*)
{
exception Eof
exception InternalError of string

open Pervasives_

module P = Cparser
module H = Hashtbl

let matchingParsOpen = ref 0

let skip_lexeme lexbuf =
  let _ = Lexing.lexeme lexbuf in
  ()

(* Keyword hashtable, c.f. 6.4.1#1 *)
let lexicon =
  List.fold_left
    (fun m (k, e) -> BatMap.add k e m)
    BatMap.empty
    [
      ("alignof",        P.ALIGNOF);
      ("auto",           P.AUTO);
      ("break",          P.BREAK);
      ("case",           P.CASE);
      ("char",           P.CHAR);
      ("const",          P.CONST);
      ("continue",       P.CONTINUE);
      ("default",        P.DEFAULT);
      ("do",             P.DO);
      ("double",         P.DOUBLE); (* LATER *)
      ("else",           P.ELSE);
      ("enum",           P.ENUM);
      ("extern",         P.EXTERN);
      ("float",          P.FLOAT); (* LATER *)
      ("for",            P.FOR);
      ("goto",           P.GOTO);
      ("if",             P.IF);
      ("inline",         P.INLINE);
      ("int",            P.INT);
      ("long",           P.LONG);
      ("register",       P.REGISTER);
      ("restrict",       P.RESTRICT);
      ("return",         P.RETURN);
      ("short",          P.SHORT);
      ("signed",         P.SIGNED);
      ("sizeof",         P.SIZEOF);
      ("static",         P.STATIC);
      ("struct",         P.STRUCT);
      ("switch",         P.SWITCH);
      ("typedef",        P.TYPEDEF);
      ("union",          P.UNION);
      ("unsigned",       P.UNSIGNED);
      ("void",           P.VOID);
      ("volatile",       P.VOLATILE);
      ("while",          P.WHILE);
      ("_Alignas",       P.ALIGNAS);
      ("_Atomic",        P.ATOMIC);
      ("_Bool",          P.BOOL);
      ("_Complex",       P.COMPLEX); (* LATER *)
      ("_Generic",       P.GENERIC);
      ("_Imaginary",     P.IMAGINARY); (* LATER *)
      ("_Noreturn",      P.NORETURN);
      ("_Static_assert", P.STATIC_ASSERT);
      ("_Thread_local",  P.THREAD_LOCAL);
    ]

(*
** Useful primitives
*)
let scan_ident lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    BatMap.find id lexicon
  (* default to variable name, as opposed to type *)
  with Not_found ->
(* (* TODO: clean *)
    if List.mem id ["extern"; "typedef"] then
      let msg =
        "The keyword \"" ^ id ^ "\" in "
        ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
        ^ " is unsupported.\n" in
      raise_error msg
    else
*)
      P.IDENT id


(*** escape character management ***)
let scan_escape (char: char) : int64 =
  let result = match char with
    | 'n' -> '\n'
    | 'r' -> '\r'
    | 't' -> '\t'
    | 'b' -> '\b'
    | 'f' -> '\012'  (* ASCII code 12 *)
    | 'v' -> '\011'  (* ASCII code 11 *)
    | 'a' -> '\007'  (* ASCII code 7 *)
    | 'e' | 'E' -> '\027'  (* ASCII code 27. This is a GCC extension *)
    | '\'' -> '\''    
    | '"'-> '"'     (* '"' *)
    | '?' -> '?'
    | '(' -> '('
    | '{' -> '{'
    | '[' -> '['
    | '%' -> '%'
    | '\\' -> '\\' 
    | other -> raise_error ("Unrecognized escape sequence: \\" ^ (String.make 1 other)) in
  Int64.of_int (Char.code result)

let valueOfDigit chr =
  let int_value = 
    match chr with
    | '0'..'9' -> (Char.code chr) - (Char.code '0')
    | 'a'..'z' -> (Char.code chr) - (Char.code 'a') + 10
    | 'A'..'Z' -> (Char.code chr) - (Char.code 'A') + 10
    | _ -> raise_error ("Character \'" ^ String.make 1 chr ^ "\' not a digit.") in
  Int64.of_int int_value

let scan_hex_escape str =
  let radix = Int64.of_int 16 in
  let the_value = ref Int64.zero in
  (* start at character 2 to skip the \x *)
  for i = 2 to (String.length str) - 1 do
    let thisDigit = valueOfDigit (String.get str i) in
    (* the_value := !the_value * 16 + thisDigit *)
    the_value := Int64.add (Int64.mul !the_value radix) thisDigit
  done;
  !the_value

let scan_oct_escape str =
  let radix = Int64.of_int 8 in
  let the_value = ref Int64.zero in
  (* start at character 1 to skip the \x *)
  for i = 1 to (String.length str) - 1 do
    let thisDigit = valueOfDigit (String.get str i) in
    (* the_value := !the_value * 8 + thisDigit *)
    the_value := Int64.add (Int64.mul !the_value radix) thisDigit
  done;
  !the_value

let lex_hex_escape remainder lexbuf =
  let prefix = scan_hex_escape (Lexing.lexeme lexbuf) in
  prefix :: remainder lexbuf

let lex_oct_escape remainder lexbuf =
  let prefix = scan_oct_escape (Lexing.lexeme lexbuf) in
  prefix :: remainder lexbuf

let lex_simple_escape remainder lexbuf =
  let lexchar = Lexing.lexeme_char lexbuf 1 in
  let prefix = scan_escape lexchar in
  prefix :: remainder lexbuf

let lex_unescaped remainder lexbuf =
  let prefix = Int64.of_int (Char.code (Lexing.lexeme_char lexbuf 0)) in
  prefix :: remainder lexbuf

let lex_comment remainder lexbuf =
  let ch = Lexing.lexeme_char lexbuf 0 in
  let prefix = Int64.of_int (Char.code ch) in
  if ch = '\n' then Lexing.new_line lexbuf;
  prefix :: remainder lexbuf

}

let letter = ['a'- 'z' 'A'-'Z']








(* 6.4.2.1#1 Identifiers, General*)
let nondigit = ['_' 'a' - 'z' 'A' - 'Z']
let digit = ['0'-'9']

(* BEGIN K *)

(* 6.4.4.1#1 Integer constants *)
let hexadecimal_prefix = "0x" | "0X"
let nonzero_digit = ['1'-'9']
let octal_digit = ['0'-'7']
let hexadecimal_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let unsigned_suffix = 'u' | 'U'
let long_suffix = 'l' | 'L'
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?
let decimal_constant = nonzero_digit digit*
let octal_constant = '0' octal_digit*
let hexadecimal_constant = hexadecimal_prefix hexadecimal_digit+
let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

(* 6.4.4.2#1 Float constants *)
(*
let floating_constant =
    decimal_floating_constant
  | hexadecimal_floating_constant

let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | digit_sequence exponent_part floating_suffix?

let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant binary_exponent_part floating_suffix?
  | hexadecimal_prefix hexadecimal_digit_sequence binary_exponent_part floating_suffix?

let fractional_constant =
    digit_sequence? '.' digit_sequence
  | digit_sequence '.'

let exponent_part =
    'e' sign? digit_sequence
  | 'E' sign? digit_sequence

let sign = ['+' '-']

let digit_sequence = digit+
(*
    digit
  | digit_sequence digit
*)

let hexadecimal_fractional_constant =
    hexadecimal_digit_sequence? '.' hexadecimal_digit_sequence
  | hexadecimal_digit_sequence '.'

let binary_exponent_part = ['p' 'P'] sign? digit-sequence
(*
    'p' sign? digit-sequence
  | 'P' sign? digit-sequence
*)

let hexadecimal_digit_sequence = hexadecimal_digit+
(*
    hexadecimal_digit
  | hexadecimal_digit_sequence hexadecimal_digit
*)

let floating_suffix = ['f' 'l' 'F' 'L']



(* 6.4.4.3 Enumeration constants *)
let enumeration_constant = identifier

(* 6.4.4.4 Character constants *)
let character_constant =
    '\'' c_char_sequence '\''
  | 'L' '\'' c_char_sequence '\''
  | 'u' '\'' c_char_sequence '\''
  | 'U' '\'' c_char_sequence '\''

let c_char_sequence = c_char+
*)


(* END K *)












let ident = (letter|'_'|'$')(letter|digit|'_'|'$')* 
let blank = [' ' '\t' '\012' '\r']+
let escape = '\\' _
(*
let hex_escape = '\\' ['x' 'X'] hexdigit+
let oct_escape = '\\' octdigit octdigit? octdigit? 
*)

rule initial = parse
| "/*" {let _ = comment lexbuf in initial lexbuf}
| "//"                    {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; initial lexbuf}
| blank		        {initial lexbuf}
| '\n'                  {Lexing.new_line lexbuf; initial lexbuf}
| '\\' '\r' * '\n'      {Lexing.new_line lexbuf; initial lexbuf}
| '#'			{hash lexbuf}
| '\''			{P.CONST_CHAR (chr lexbuf)}
| "L'"			{P.CONST_WCHAR (chr lexbuf)}
| '"'			{skip_lexeme lexbuf; (* '"' *)
(* matth: BUG:  this could be either a regular string or a wide string.
 *  e.g. if it's the "world" in 
 *     L"Hello, " "world"
 *  then it should be treated as wide even though there's no L immediately
 *  preceding it.  See test/small1/wchar5.c for a failure case. *)
                          try P.CONST_STRING (str lexbuf)
                          with e -> 
                            raise (InternalError 
                                     ("str: " ^ 
                                         Printexc.to_string e))}
| "L\""			{ (* weimer: wchar_t string literal *)
                                          try P.CONST_WSTRING(str lexbuf)
                                          with e -> 
                                             raise (InternalError 
                                                     ("wide string: " ^ 
                                                      Printexc.to_string e))}
(* TODO Re-enabled exluded constants.
| floatnum		{P.CONST_FLOAT (Lexing.lexeme lexbuf, currentLoc ())}
| hexnum			{P.CONST_INT (Lexing.lexeme lexbuf, currentLoc ())}
| octnum			{P.CONST_INT (Lexing.lexeme lexbuf, currentLoc ())}
*)
| decimal_constant
    { let num = Lexing.lexeme lexbuf in
      integer_suffix lexbuf (Nat_num.num_of_string num)
    }
| hexadecimal_constant
    { let num = Lexing.lexeme lexbuf in
      integer_suffix lexbuf (Nat_num.num_of_string num)
    }
(* TODO Hack alert! We do not lex octal numbers but "0" is an octal number. :( *)
| "0"
    { let num = Lexing.lexeme lexbuf in
      integer_suffix lexbuf (Nat_num.num_of_string num)
    }
| "+="	{P.PLUS_EQ}
| "-="	{P.MINUS_EQ}
| "*="	{P.STAR_EQ}
| "/="	{P.SLASH_EQ}
| "%="	{P.PERCENT_EQ}
| "|="	{P.PIPE_EQ}
| "&="	{P.AND_EQ}
| "^="	{P.CIRC_EQ}
| "<<="	{P.INF_INF_EQ}
| ">>="	{P.SUP_SUP_EQ}
| "<<"	{P.INF_INF}
| ">>"	{P.SUP_SUP}
| "=="	{P.EQ_EQ}
| "!="	{P.EXCLAM_EQ}
| "<="	{P.INF_EQ}
| ">="	{P.SUP_EQ}
| "="	{P.EQ}
| "<"	{P.INF}
| ">"	{P.SUP}
| "++"	{P.PLUS_PLUS}
| "--"	{P.MINUS_MINUS}
| "->"	{P.ARROW}
| '+'	{P.PLUS}
| '-'	{P.MINUS}
| '*'	{P.STAR}
| '/'	{P.SLASH}
| '%'	{P.PERCENT}
| '!'	{P.EXCLAM}
| "&&"	{P.AND_AND}
| "||"	{P.PIPE_PIPE}
| '&'	{P.AND}
| '|'	{P.PIPE}
| '^'	{P.CIRC}
| '?'	{P.QUEST}
| ':'	{P.COLON}
| '~'	{P.TILDE}	
| '{'   {P.LBRACE}
| '}'	{P.RBRACE}
| '['	{P.LBRACKET}
| ']'	{P.RBRACKET}
| '('	{P.LPAREN}
| ')'	{P.RPAREN}
| ';'	{P.SEMICOLON}
| ','	{P.COMMA}
| '.'	{P.DOT}
| "sizeof" {P.SIZEOF}
(* __extension__ is a black. The parser runs into some conflicts if we let it
 * pass *)
| "__extension__"         {initial lexbuf}
| ident			{scan_ident lexbuf}
| eof			{P.EOF}
| _
    { raise_error ("Unexpected symbol \""
                   ^ Lexing.lexeme lexbuf ^ "\" in "
                   ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
                   ^ ".\n")
    }
and comment =
    parse 	
      "*/"			        {[]}
(*| '\n'                              {Lexing.new_line lexbuf; lex_unescaped comment lexbuf}*)
| _ 			{lex_comment comment lexbuf}


and onelinecomment = parse
    '\n'|eof    {[]}
| _           {lex_comment onelinecomment lexbuf}

and matchingpars = parse
  '\n'          {Lexing.new_line lexbuf; matchingpars lexbuf}
| blank         {matchingpars lexbuf}
| '('           {incr matchingParsOpen; matchingpars lexbuf}
| ')'           {decr matchingParsOpen;
                  if !matchingParsOpen = 0 then 
                     ()
                  else 
                     matchingpars lexbuf
                }
| "/*"		{ let _ = comment lexbuf in matchingpars lexbuf}
| '"'		{(* '"' *)
                  let _ = str lexbuf in 
                  matchingpars lexbuf
                 }
| _              {matchingpars lexbuf}

(* # <line number> <file name> ... *)
and hash = parse
  '\n'		{Lexing.new_line lexbuf; initial lexbuf}
| blank		{hash lexbuf}
(*
| intnum	{(* We are seeing a line number. This is the number for the 
                   * next line *)
                 let s = Lexing.lexeme lexbuf in
                 let lineno = try
                   int_of_string s
                 with Failure ("int_of_string") ->
                   (* the int is too big. *)
                   E.warn "Bad line number in preprocessed file: %s" s;
                   (-1)
                 in
                  E.setCurrentLine (lineno - 1);
                  (* A file name may follow *)
		  file lexbuf}
| "line"        {hash lexbuf} (* MSVC line number info *)
| _	        {endline lexbuf}

and file =  parse 
| '\n'		        {Lexing.new_line lexbuf; initial lexbuf}
| blank			{file lexbuf}
| '"' [^ '\012' '\t' '"']* '"' { (* '"' *)
                                       let n = Lexing.lexeme lexbuf in
                                       let n1 = String.sub n 1 ((String.length n) - 2) in
                                       E.setCurrentFile n1;
				       endline lexbuf}

| _			{endline lexbuf}
*)

and endline = parse 
        '\n' 			{Lexing.new_line lexbuf; initial lexbuf}
| eof                         {P.EOF}
| _			{endline lexbuf}


and str = parse
        '"'             {[]} (* no nul terminiation in CST_STRING '"' *)
(*
| hex_escape	{skip_lexeme lexbuf; lex_hex_escape str lexbuf}
| oct_escape	{skip_lexeme lexbuf; lex_oct_escape str lexbuf}
*)
| escape		{skip_lexeme lexbuf; lex_simple_escape str lexbuf}
| _		{skip_lexeme lexbuf; lex_unescaped str lexbuf}

and chr =  parse
	'\''	        {[]}
(*| hex_escape	{lex_hex_escape chr lexbuf}
| oct_escape	{lex_oct_escape chr lexbuf}
*)
| escape		{lex_simple_escape chr lexbuf}
| _		{lex_unescaped chr lexbuf}

(* 6.4.4.1#1 Integer Constants, Syntax - integer-suffix *)
and integer_suffix = parse
  | unsigned_suffix long_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED_LONG)}
  | unsigned_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED)}
  | long_suffix unsigned_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED_LONG)}
  | long_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_LONG)}
  | long_long_suffix unsigned_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED_LONG_LONG)}
  | long_long_suffix
      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_LONG_LONG)}
  | ""
      {fun n -> P.CONST_INT (n, None)}

{
}
