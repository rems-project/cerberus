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
module E = Errormsg
module H = Hashtbl

let matchingParsOpen = ref 0

let currentLoc () = Cabshelper.currentLoc ()

(* string -> unit *)
let addComment c =
  let l = currentLoc() in
  let i = GrowArray.max_init_index Cabshelper.commentsGA in
  GrowArray.setg Cabshelper.commentsGA (i+1) (l,c,false)

(* track whitespace for the current token *)
let white = ref ""

let addWhite lexbuf =
  if not !Whitetrack.enabled then
    let w = Lexing.lexeme lexbuf in 
    white := !white ^ w
let clear_white () = white := ""
let get_white () = !white

let lexeme = ref ""
let addLexeme lexbuf =
    let l = Lexing.lexeme lexbuf in
    lexeme := !lexeme ^ l
let clear_lexeme () = lexeme := ""
let get_extra_lexeme () = !lexeme 

let int64_to_char value =
  if (compare value (Int64.of_int 255) > 0) || (compare value Int64.zero < 0) then
    begin
      let msg = Printf.sprintf "clexer:intlist_to_string: character 0x%Lx too big" value in
      E.parse_error msg;
    end
  else
    Char.chr (Int64.to_int value)

(* takes a not-nul-terminated list, and converts it to a string. *)
let rec intlist_to_string (str: int64 list):string =
  match str with
    [] -> ""  (* add nul-termination *)
  | value::rest ->
      let this_char = int64_to_char value in
      (String.make 1 this_char) ^ (intlist_to_string rest)

(* Some debugging support for line numbers *)
let dbgToken (t: P.token) =
  let format = function
    | P.IDENT n -> Pretty.dprintf "IDENT(%s)\n" n
    | P.LBRACE -> Pretty.dprintf "LBRACE\n"
    | P.RBRACE -> Pretty.dprintf "RBRACE\n"
    | P.IF -> Pretty.dprintf "IF\n"
    | P.SWITCH -> Pretty.dprintf "SWITCH\n"
    | P.RETURN -> Pretty.dprintf "RETURN\n"
    | _ -> Pretty.nil
  in
  if false then
    let () = E.log "%a" Pretty.insert (format t) in
    t
  else t

(* Keyword hashtable, c.f. 6.4.1#1 *)
let lexicon = H.create 211
let init_lexicon _ =
  H.clear lexicon;
  List.iter 
    (fun (key, builder) -> H.add lexicon key builder)
    [ ("auto", P.AUTO);
      ("const", P.CONST);
      ("static", P.STATIC);
      ("long", P.LONG);
      ("short", P.SHORT);
      ("signed", P.SIGNED);
      ("unsigned", P.UNSIGNED);
      ("volatile", P.VOLATILE);
      ("_Bool", P.BOOL);
      ("char", P.CHAR);
      ("int", P.INT);
      ("void", P.VOID);
      ("enum", P.ENUM);
      ("struct", P.STRUCT);
      ("union", P.UNION);
      ("break", P.BREAK);
      ("continue", P.CONTINUE);
      ("goto", P.GOTO); 
      ("return", dbgToken P.RETURN);
      ("switch", dbgToken P.SWITCH);
      ("case", P.CASE); 
      ("default", P.DEFAULT);
      ("while", P.WHILE);  
      ("do", P.DO);  
      ("for", P.FOR);
      ("if", dbgToken P.IF);
      ("else", P.ELSE);
      ("inline", P.INLINE);
    ]

let context : string list list ref = ref []

let push_context _ = context := []::!context

let pop_context _ = 
  match !context with
    [] -> raise (InternalError "Empty context stack")
  | con::sub ->
		(context := sub;
		List.iter (fun name -> 
                           (* ignore (print_string ("removing lexicon for " ^ name ^ "\n")); *)
                            H.remove lexicon name) con)

(* Mark an identifier as a variable name. The old mapping is preserved and 
 * will be reinstated when we exit this context  *)
let add_identifier name =
  match !context with
    [] -> () (* Just ignore raise (InternalError "Empty context stack") *)
  | con::sub ->
      (context := (name::con)::sub;
       (*                print_string ("adding IDENT for " ^ name ^ "\n"); *)
       H.add lexicon name (dbgToken (P.IDENT name)))


(*
** Useful primitives
*)
let scan_ident lexbuf =
  let id = Lexing.lexeme lexbuf in
  try H.find lexicon id
  (* default to variable name, as opposed to type *)
  with Not_found ->
(*
    if id.[0] = '$' then P.QUALIFIER (id) else
*)
    if List.mem id ["extern"; "typedef"] then
      let msg =
        "The keyword \"" ^ id ^ "\" in "
        ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
        ^ " is unsupported.\n" in
      raise_error msg
    else
      dbgToken (P.IDENT id)


(*
** Buffer processor
*)
 

let init lexbuf =
  init_lexicon ();
  (* Inititialize the pointer in Errormsg *)
  Lexerhack.push_context := push_context;
  Lexerhack.pop_context := pop_context;
  Lexerhack.add_identifier := add_identifier;
  E.startParsing lexbuf


let finish () = 
  E.finishParsing ()

(*** Error handling ***)
let error msg =
  E.parse_error msg


(*** escape character management ***)
let scan_escape (char: char) : int64 =
  let result = match char with
    'n' -> '\n'
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
  | other -> error ("Unrecognized escape sequence: \\" ^ (String.make 1 other))
  in
  Int64.of_int (Char.code result)

let scan_hex_escape str =
  let radix = Int64.of_int 16 in
  let the_value = ref Int64.zero in
  (* start at character 2 to skip the \x *)
  for i = 2 to (String.length str) - 1 do
    let thisDigit = Cabshelper.valueOfDigit (String.get str i) in
    (* the_value := !the_value * 16 + thisDigit *)
    the_value := Int64.add (Int64.mul !the_value radix) thisDigit
  done;
  !the_value

let scan_oct_escape str =
  let radix = Int64.of_int 8 in
  let the_value = ref Int64.zero in
  (* start at character 1 to skip the \x *)
  for i = 1 to (String.length str) - 1 do
    let thisDigit = Cabshelper.valueOfDigit (String.get str i) in
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
  if ch = '\n' then E.newline();
  prefix :: remainder lexbuf

let make_char (i:int64):char =
  let min_val = Int64.zero in
  let max_val = Int64.of_int 255 in
  (* if i < 0 || i > 255 then error*)
  if compare i min_val < 0 || compare i max_val > 0 then begin
    let msg = Printf.sprintf "clexer:make_char: character 0x%Lx too big" i in
    error msg
  end;
  Char.chr (Int64.to_int i)


(* ISO standard locale-specific function to convert a wide character
 * into a sequence of normal characters. Here we work on strings. 
 * We convert L"Hi" to "H\000i\000" 
  matth: this seems unused.
let wbtowc wstr =
  let len = String.length wstr in 
  let dest = String.make (len * 2) '\000' in 
  for i = 0 to len-1 do 
    dest.[i*2] <- wstr.[i] ;
  done ;
  dest
*)

(* This function converst the "Hi" in L"Hi" to { L'H', L'i', L'\0' }
  matth: this seems unused.
let wstr_to_warray wstr =
  let len = String.length wstr in
  let res = ref "{ " in
  for i = 0 to len-1 do
    res := !res ^ (Printf.sprintf "L'%c', " wstr.[i])
  done ;
  res := !res ^ "}" ;
  !res
*)

}

let letter = ['a'- 'z' 'A'-'Z']

let unsigned_suffix = 'u' | 'U'
let long_suffix = 'l' | 'L'
let long_long_suffix = "ll" | "LL"
let digit = ['0'-'9']
let nonzero_digit = ['1'-'9']

let decimal_constant = nonzero_digit digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hexadecimal_constant = hexadecimal_prefix hexadecimal_digit+

let lsuffix = long_suffix | long_long_suffix
let usuffix = unsigned_suffix
let intsuffix = lsuffix | usuffix | usuffix lsuffix | lsuffix usuffix | usuffix
let intnum = digit+ intsuffix?
(*
let octdigit = ['0'-'7']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']

let hexprefix = '0' ['x' 'X']

let octnum = '0' octdigit+ intsuffix?
let hexnum = hexprefix hexdigit+ intsuffix?
*)

let exponent = ['e' 'E']['+' '-']? digit+
let fraction  = '.' digit+
let decfloat = (intnum? fraction)
	      |(intnum exponent)
	      |(intnum? fraction exponent)
	      | (intnum '.') 
              | (intnum '.' exponent) 

(*
let hexfraction = hexdigit* '.' hexdigit+ | hexdigit+
let binexponent = ['p' 'P'] ['+' '-']? digit+
let hexfloat = hexprefix hexfraction binexponent
             | hexprefix hexdigit+   binexponent

let floatsuffix = ['f' 'F' 'l' 'L']
let floatnum = (decfloat | hexfloat) floatsuffix?
*)

let ident = (letter|'_'|'$')(letter|digit|'_'|'$')* 
let blank = [' ' '\t' '\012' '\r']+
let escape = '\\' _
(*
let hex_escape = '\\' ['x' 'X'] hexdigit+
let oct_escape = '\\' octdigit octdigit? octdigit? 
*)

rule initial = parse
| "/*"			{ let il = comment lexbuf in
	                                  let sl = intlist_to_string il in
					  addComment sl;
                                          addWhite lexbuf;
                                          initial lexbuf}
| "//"                    { let il = onelinecomment lexbuf in
                                          let sl = intlist_to_string il in
                                          addComment sl;
                                          E.newline();
                                          addWhite lexbuf;
                                          initial lexbuf
                                           }
| blank			{ addWhite lexbuf; initial lexbuf}
| '\n'                    { E.newline ();
                                            addWhite lexbuf;
                                            initial lexbuf
                                        }
| '\\' '\r' * '\n'        { addWhite lexbuf;
                                          E.newline ();
                                          initial lexbuf
                                        }
| '#'			{ addWhite lexbuf; hash lexbuf}
| '\''			{ P.CONST_CHAR (chr lexbuf)}
| "L'"			{ P.CONST_WCHAR (chr lexbuf) }
| '"'			{ addLexeme lexbuf; (* '"' *)
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
| "!quit!"		{P.EOF}
| "+="			{P.PLUS_EQ}
| "-="			{P.MINUS_EQ}
| "*="			{P.STAR_EQ}
| "/="			{P.SLASH_EQ}
| "%="			{P.PERCENT_EQ}
| "|="			{P.PIPE_EQ}
| "&="			{P.AND_EQ}
| "^="			{P.CIRC_EQ}
| "<<="			{P.INF_INF_EQ}
| ">>="			{P.SUP_SUP_EQ}
| "<<"			{P.INF_INF}
| ">>"			{P.SUP_SUP}
| "=="			{P.EQ_EQ}
| "!="			{P.EXCLAM_EQ}
| "<="			{P.INF_EQ}
| ">="			{P.SUP_EQ}
| "="				{P.EQ}
| "<"				{P.INF}
| ">"				{P.SUP}
| "++"			{P.PLUS_PLUS}
| "--"			{P.MINUS_MINUS}
| "->"			{P.ARROW}
| '+'				{P.PLUS}
| '-'				{P.MINUS}
| '*'				{P.STAR}
| '/'				{P.SLASH}
| '%'				{P.PERCENT}
| '!'			{P.EXCLAM}
| "&&"			{P.AND_AND}
| "||"			{P.PIPE_PIPE}
| '&'				{P.AND}
| '|'				{P.PIPE}
| '^'				{P.CIRC}
| '?'				{P.QUEST}
| ':'				{P.COLON}
| '~'		       {P.TILDE}
	
| '{'		       {dbgToken (P.LBRACE)}
| '}'		       {dbgToken (P.RBRACE)}
| '['				{P.LBRACKET}
| ']'				{P.RBRACKET}
| '('		       {dbgToken (P.LPAREN) }
| ')'				{P.RPAREN}
| ';'		       {dbgToken (P.SEMICOLON) }
| ','				{P.COMMA}
| '.'				{P.DOT}
| "sizeof"		{P.SIZEOF}

(* __extension__ is a black. The parser runs into some conflicts if we let it
 * pass *)
| "__extension__"         {addWhite lexbuf; initial lexbuf }
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
      "*/"			        { addWhite lexbuf; [] }
(*| '\n'                              { E.newline (); lex_unescaped comment lexbuf }*)
| _ 			{ addWhite lexbuf; lex_comment comment lexbuf }


and onelinecomment = parse
    '\n'|eof    {addWhite lexbuf; []}
| _           {addWhite lexbuf; lex_comment onelinecomment lexbuf }

and matchingpars = parse
  '\n'          { addWhite lexbuf; E.newline (); matchingpars lexbuf }
| blank         { addWhite lexbuf; matchingpars lexbuf }
| '('           { addWhite lexbuf; incr matchingParsOpen; matchingpars lexbuf }
| ')'           { addWhite lexbuf; decr matchingParsOpen;
                  if !matchingParsOpen = 0 then 
                     ()
                  else 
                     matchingpars lexbuf
                }
| "/*"		{ addWhite lexbuf; let il = comment lexbuf in
                  let sl = intlist_to_string il in
		  addComment sl;
                  matchingpars lexbuf}
| '"'		{ addWhite lexbuf; (* '"' *)
                  let _ = str lexbuf in 
                  matchingpars lexbuf
                 }
| _              { addWhite lexbuf; matchingpars lexbuf }

(* # <line number> <file name> ... *)
and hash = parse
  '\n'		{ addWhite lexbuf; E.newline (); initial lexbuf}
| blank		{ addWhite lexbuf; hash lexbuf}
| intnum	{ addWhite lexbuf; (* We are seeing a line number. This is the number for the 
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
		  file lexbuf }
| "line"        { addWhite lexbuf; hash lexbuf } (* MSVC line number info *)
| _	        { addWhite lexbuf; endline lexbuf}

and file =  parse 
| '\n'		        {addWhite lexbuf; E.newline (); initial lexbuf}
| blank			{addWhite lexbuf; file lexbuf}
| '"' [^ '\012' '\t' '"']* '"' { addWhite lexbuf;  (* '"' *)
                                       let n = Lexing.lexeme lexbuf in
                                       let n1 = String.sub n 1 ((String.length n) - 2) in
                                       E.setCurrentFile n1;
				       endline lexbuf}

| _			{addWhite lexbuf; endline lexbuf}

and endline = parse 
        '\n' 			{ addWhite lexbuf; E.newline (); initial lexbuf}
| eof                         { P.EOF }
| _			{ addWhite lexbuf; endline lexbuf}


and str = parse
        '"'             {[]} (* no nul terminiation in CST_STRING '"' *)
(*
| hex_escape	{addLexeme lexbuf; lex_hex_escape str lexbuf}
| oct_escape	{addLexeme lexbuf; lex_oct_escape str lexbuf}
*)
| escape		{addLexeme lexbuf; lex_simple_escape str lexbuf}
| _		{addLexeme lexbuf; lex_unescaped str lexbuf}

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
