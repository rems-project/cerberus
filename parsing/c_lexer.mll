{
exception Eof
exception InternalError of string

open Pervasives_

module P = C_parser
module H = Hashtbl

type token = P.token

(* used by [matchingpars] *)
let matchingParsOpen = ref 0

(* TODO: document *)
let skip_lexeme lexbuf =
  let _ = Lexing.lexeme lexbuf in
  ()

(* 6.4 [Lexical elements]
    
    token:
        keyword
        identifier
        constant
        string-literal
        punctuator
    
    preprocessing-token:
        header-name
        identifier
        pp-number
        character-constant
        string-literal
        punctuator
        "each non-white-space character that cannot be one of the above"
*)

(* 6.4.1 [Keywords] *)
let keywords =
  List.fold_left
    (fun m (k, e) -> Pmap.add k e m)
    (Pmap.empty Pervasives.compare)
    [
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
      ("_Alignog",       P.ALIGNOF);
      ("_Atomic",        P.ATOMIC);
      ("_Bool",          P.BOOL);
      ("_Complex",       P.COMPLEX); (* LATER *)
      ("_Generic",       P.GENERIC);
      ("_Imaginary",     P.IMAGINARY); (* LATER *)
      ("_Noreturn",      P.NORETURN);
      ("_Static_assert", P.STATIC_ASSERT);
      ("_Thread_local",  P.THREAD_LOCAL);
    ]



(* Return a keyword or a identifier (TODO: this is not using the proper regexp
   for identifiers) *)
let scan_ident lexbuf =
  let id = Lexing.lexeme lexbuf in
  try
    Pmap.find id keywords
  (* default to variable name, as opposed to type *)
  with Not_found ->
    (* Check if the token is an enumeration constant *)
      P.IDENTIFIER id



(* TODO: READ *)

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














(* TODO *)
(* §5.2.1 *)

let uppercase_letters  = ['A'-'Z']
let lowercase_letters  = ['a'-'z']
let digits             = ['0'-'9']
let graphic_characters = ['!' '"' '#' '%' '&' '\'' '('  ')' '*' '+' ',' '-' '.' '/' ':'
                          ';' '<' '=' '>' '?' '['  '\\' ']' '^' '_' '{' '|' '}' '~']

let basic_character_set =
    uppercase_letters
  | lowercase_letters
  | digits
  | graphic_characters



(* ================== BEGIN NEW LEXER ================== *)

(* defined in §6.4.4.1#1 *)
let nonzero_digit = ['1'-'9']

(* defined in §6.4.2.1#1 *)
let digit = ['0' - '9']

(* defined in §6.4.4.1#1 *)
let decimal_constant = nonzero_digit digit*
let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*
let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hexadecimal_constant = hexadecimal_prefix hexadecimal_digit+
let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?
let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

(* defined in §6.4.3#1 *)
let hex_quad = hexadecimal_digit hexadecimal_digit hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

(* defined in §6.4.2.1#1 *)
let nondigit = ['_' 'a' - 'z' 'A' - 'Z']
let identifier_nondigit =
    nondigit
  | universal_character_name
    (* TODO: "other implementation-defined characters" *)
let identifier = identifier_nondigit (identifier_nondigit | digit)*

(* defined in §6.4.4.2#1 *)
let digit_sequence = digit+
let fractional_constant =
    digit_sequence? '.' digit_sequence
  | digit_sequence '.'
let sign = ['+' '-']
let exponent_part = ['e' 'E'] sign? digit_sequence
let floating_suffix = ['f' 'l' 'F' 'L']
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | digit_sequence exponent_part floating_suffix?
let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    hexadecimal_digit_sequence? '.' hexadecimal_digit_sequence
  | hexadecimal_digit_sequence '.'
let binary_exponent_part = ['p' 'P'] sign? digit_sequence
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant binary_exponent_part floating_suffix?
  | hexadecimal_prefix hexadecimal_digit_sequence binary_exponent_part floating_suffix?
let floating_constant =
    decimal_floating_constant
  | hexadecimal_floating_constant

(* defined in §6.4.4.3#1 *)
let enumeration_constant = identifier

(* defined in §6.4.4.4#1 *)
let simple_escape_sequence = ("\\'" | "\\\"" | "\\?" | "\\\\" | "\\a" | "\\b" | "\\f" | "\\n" | "\\r" | "\\t" | "\\v")
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
    ['a'-'z' 'A'-'Z'] (* TODO: "any member of the source character set except the single-quote ', backslash \, or new-line character" *)
  | escape_sequence
let c_char_sequence = c_char+
let character_constant = ("'" | "L'" | "u'" | "U'") c_char_sequence '\''

(* defined in §6.4.4#1 *)
let constant =
    integer_constant
  | floating_constant
  | enumeration_constant
  | character_constant

(* defined in §6.4.5#1 *)
let encoding_prefix = ("u8" | "u" | "U" | "L")
let s_char =
    ['a'-'z'] (* TODO: any member of the source character set except the double-quote , backslash \, or new-line character *)
  | escape_sequence
let s_char_sequence = s_char+
let string_literal = encoding_prefix? '"' s_char_sequence? '"' (* USELESS *)

(* defined in §6.4.7#1 *)
let h_char =
  ['a'-'z'] (* TODO: any member of the source character set except the new-line character and > *)
let h_char_sequence = h_char+
let q_char = ['a'-'z'] (*TODO: any member of the source character set except the new-line character and  *)
let q_char_sequence = q_char+
let header_name =
    '<' h_char_sequence '>'
  | '"' q_char_sequence '"'

(* defined in §6.4.8#1 *)
let pp_number = (digit | '.' digit) (digit | identifier_nondigit | 'e' sign | 'E' sign | 'p' sign | 'P' sign | '.')*
(* ================== END NEW LEXER ================== *)










let escape = "" (* TODO *)




















let blank = [' ' '\t' '\012' '\r']+



(* ================================ BEGIN CLEAN ============================= *)

(* Entry point to the lexer *)
rule main = parse
  (* Beginning of a comment *)
  | "/*" {let _ = comment lexbuf in main lexbuf}
  
  (* Single-line comment *)
  | "//" {let _ = onelinecomment lexbuf in Lexing.new_line lexbuf; main lexbuf}
  
  (* Skip blanks *)
  | blank {main lexbuf}
  
  (* §6.4.4.1 Integer constants, Syntax *)
  | decimal_constant
  | octal_constant
  | hexadecimal_constant {let num = Lexing.lexeme lexbuf in
                          integer_suffix lexbuf (Nat_num.num_of_string num)}
  
  (* (§6.4.6#1) Punctuators *)
  | ']'	   {P.RBRACKET}
  | '['	   {P.LBRACKET}
  | '('	   {P.LPAREN}
  | ')'	   {P.RPAREN}
  | '{'    {P.LBRACE}
  | '}'    {P.RBRACE}
  | "{{{"  {P.LBRACES_3}
  | "}}}"  {P.RBRACES_3}
  | "|||"  {P.PIPES_3}
  | '.'    {P.DOT}
  | "->"   {P.ARROW}
  | "++"   {P.PLUS_PLUS}
  | "--"   {P.MINUS_MINUS}
  | '&'    {P.AND}
  | '*'    {P.STAR}
  | '+'    {P.PLUS}
  | '-'    {P.MINUS}
  | '~'    {P.TILDE}	
  | '!'    {P.EXCLAM}
  | '/'    {P.SLASH}
  | '%'    {P.PERCENT}
  | "<<"   {P.INF_INF}
  | ">>"   {P.SUP_SUP}
  | "<"	   {P.INF}
  | ">"    {P.SUP}
  | "<="   {P.INF_EQ}
  | ">="   {P.SUP_EQ}
  | "=="   {P.EQ_EQ}
  | "!="   {P.EXCLAM_EQ}
  | '^'	   {P.CIRC}
  | '|'	   {P.PIPE}
  | "&&"   {P.AND_AND}
  | "||"   {P.PIPE_PIPE}
  | '?'	   {P.QUEST}
  | ':'	   {P.COLON}
  | ';'	   {P.SEMICOLON}
  | "..."  {P.ELLIPSIS}
  | "="	   {P.EQ}
  | "*="   {P.STAR_EQ}
  | "/="   {P.SLASH_EQ}
  | "%="   {P.PERCENT_EQ}
  | "+="   {P.PLUS_EQ}
  | "-="   {P.MINUS_EQ}
  | "<<="  {P.INF_INF_EQ}
  | ">>="  {P.SUP_SUP_EQ}
  | "&="   {P.AND_EQ}
  | "^="   {P.CIRC_EQ}
  | "|="   {P.PIPE_EQ}
  | ','	   {P.COMMA}
  | '#'    {hash lexbuf} (* TODO: CHECK *)
  (* TODO: ## *)
  (* See §64.6.6#3 for the following *)
  | "<:"   {P.LBRACKET}
  | ":>"   {P.RBRACKET}
  | "<%"   {P.LBRACE}
  | "%>"   {P.RBRACE}
  | "%:"   {hash lexbuf} (* TODO: CHECK *)
  (* TODO: "%:%:" *)




(* ================================ END CLEAN =============================== *)






| '\n'                  {Lexing.new_line lexbuf; main lexbuf}
| '\\' '\r' * '\n'      {Lexing.new_line lexbuf; main lexbuf}
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

(* TODO Hack alert! We do not lex octal numbers but "0" is an octal number. :( *)
| "0"
    { let num = Lexing.lexeme lexbuf in
      integer_suffix lexbuf (Nat_num.num_of_string num)
    }






(* | "sizeof" {P.SIZEOF} (* TODO: why was this here ? *) *)
| "\"" {P.DQUOTE}
(* __extension__ is a black. The parser runs into some conflicts if we let it
 * pass *)
| "__extension__"         {main lexbuf}
| identifier		  {scan_ident lexbuf}
| eof		          {P.EOF}
| _
    { raise_error ("Unexpected symbol \""
                   ^ Lexing.lexeme lexbuf ^ "\" in "
                   ^ Position.lines_to_string (Position.from_lexbuf lexbuf)
                   ^ ".\n")
    }







(* ================================ BEGIN CLEAN ============================= *)
(* 6.4.4 Constants *)
(*
and constant = parse
  | integer_constant
  | floating_constant
  | enumeration_constant
  | character_constant 

and integer_
*)


(* defined in 6.4.4.1#1 (Integer Constants, Syntax) *)
and integer_suffix = parse
  | unsigned_suffix                  {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED)}
  | unsigned_suffix long_suffix
  | long_suffix unsigned_suffix      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED_LONG)}
  | long_suffix                      {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_LONG)}
  | unsigned_suffix long_long_suffix
  | long_long_suffix unsigned_suffix {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_UNSIGNED_LONG_LONG)}
  | long_long_suffix                 {fun n -> P.CONST_INT (n, Some Cabs.SUFFIX_LONG_LONG)}
  | ""                               {fun n -> P.CONST_INT (n, None)}


(* ================================ END CLEAN =============================== *)


















(* Consume a comment: /* ... */ *)
and comment = parse
  (* End of the comment *)
  | "*/" {[]}
  | _    {lex_comment comment lexbuf}


(* Consume a singleline comment: // ... *)
and onelinecomment = parse
  | '\n' | eof {[]}
  | _          {lex_comment onelinecomment lexbuf}

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
  '\n'		{Lexing.new_line lexbuf; main lexbuf}
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
| '\n'		        {Lexing.new_line lexbuf; main lexbuf}
| blank			{file lexbuf}
| '"' [^ '\012' '\t' '"']* '"' { (* '"' *)
                                       let n = Lexing.lexeme lexbuf in
                                       let n1 = String.sub n 1 ((String.length n) - 2) in
                                       E.setCurrentFile n1;
				       endline lexbuf}

| _			{endline lexbuf}
*)

and endline = parse 
        '\n' 			{Lexing.new_line lexbuf; main lexbuf}
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


{
}

