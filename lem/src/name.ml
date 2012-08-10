open Format
open Pp

(* These compare faster than Ulib.Text.t *)
(*
type t = Ulib.UTF8.t
let compare r1 r2 = 
  Ulib.UTF8.compare r1 r2

let from_rope r = Ulib.Text.to_string r

let to_rope n = Ulib.Text.of_string n
let to_string = Ulib.UTF8.to_string
*)

type t = string
let compare r1 r2 = 
  Pervasives.compare r1 r2

let from_rope r = Ulib.Text.to_string r

let to_rope n = Ulib.Text.of_string n
let to_string n = n

  (*
type t = Ulib.Text.t
let compare r1 r2 = 
  if r1 == r2 then 
    0 
  else 
    Ulib.Text.compare r1 r2

let from_rope r = r

let to_rope n = n
let to_string n = Ulib.Text.to_string n
   *)

let (^) = Ulib.Text.(^^^)

let fresh_start start s ok =
  let rec f (n:int) =
    let name = s ^ Ulib.Text.of_latin1 (string_of_int n) in
      if ok (from_rope name) then 
        name
      else
        f (n + 1)
  in
  let x = s in
    match start with
      | None ->
          if ok (from_rope x) then
            x 
          else
            f 0
      | Some(i) ->
          f i

let fresh s ok = from_rope (fresh_start None s ok)

let rec fresh_list i s ok =
  if i = 0 then
    []
  else
    from_rope (fresh_start (Some(i)) s ok) :: fresh_list (i - 1) s ok

let rename f r = from_rope (f (to_rope r))

let pp ppf n = pp_str ppf (to_string n)

let starts_with_upper_letter x = 
  try 
    let c = Ulib.UChar.char_of (Ulib.UTF8.get x 0) in
      Str.string_match (Str.regexp "[A-Z]") (String.make 1 c) 0
  with 
    | Ulib.UChar.Out_of_range -> false

let starts_with_lower_letter x = 
  try 
    let c = Ulib.UChar.char_of (Ulib.UTF8.get x 0) in
      Str.string_match (Str.regexp "[a-z]") (String.make 1 c) 0
  with 
    | Ulib.UChar.Out_of_range -> false

let uncapitalize x = 
  assert (starts_with_upper_letter x);
  let c = Ulib.UChar.of_char (Char.lowercase (Ulib.UChar.char_of (Ulib.UTF8.get x 0))) in
    from_rope (Ulib.Text.set (to_rope x) 0 c)

let capitalize x =
  assert (starts_with_lower_letter x);
  let c = Ulib.UChar.of_char (Char.uppercase (Ulib.UChar.char_of (Ulib.UTF8.get x 0))) in
    from_rope (Ulib.Text.set (to_rope x) 0 c)

type name_type =
  | Bquote
  | Paren of Ast.lex_skips * Ast.lex_skips
  | Plain

type lskips_t = Ast.lex_skips * Ulib.Text.t * name_type

let from_ix = function 
  | Ast.SymX_l((s,x),l) -> (s,x,Plain)
  | Ast.InX_l(s,(None,x),None,l) -> (s,x,Bquote)
  | _ -> assert false

let from_x = function 
  | Ast.X_l((s,x),l) -> (s,x,Plain)
  | Ast.PreX_l(s1,(s2,x),s3,l) -> (s2,x,Paren(s1,s3))

let strip_lskip (_,x,_) = from_rope x

let add_lskip n = 
  (None,to_rope n,Plain)

let to_output a (s,x,nt)= 
  let open Output in
    match nt with
      | Plain -> ws s ^ id a x
      (* TODO : Parens might not be correct for all targets *)
      | Paren(s1,s2) -> 
          ws s1 ^ kwd "(" ^ ws s ^ id a x ^ ws s2 ^ kwd ")"
      (* TODO : Bquote might not be correct for all targets *)
      | Bquote -> 
          ws s ^ kwd "`" ^ id a x ^ kwd "`"

let r = Ulib.Text.of_latin1

let to_output_quoted a (s,x,nt)= 
  let open Output in
  let (^^) = Ulib.Text.(^^^) in
    match nt with
      | Plain -> ws s ^ id a (r"\"" ^^ x ^^ r"\"")
      (* TODO : Parens might not be correct for all targets *)
      | Paren(s1,s2) -> 
          ws s1 ^ kwd "(" ^ ws s ^ id a (r"\"" ^^ x ^^ r"\"") ^ ws s2 ^ kwd ")"
      (* TODO : Bquote might not be correct for all targets *)
      | Bquote -> 
          ws s ^ kwd "`" ^ id a (r"\"" ^^ x ^^ r"\"") ^ kwd "`"

let to_rope_tex a n = 
  Output.to_rope_ident a (to_rope n)

let add_pre_lskip lskip (s,x,nt) = 
  match nt with
    | Plain | Bquote ->
        (Ast.combine_lex_skips lskip s,x,nt)
    | Paren(s1,s2) ->
        (s,x,Paren(Ast.combine_lex_skips lskip s1,s2))

let get_lskip (s,x,nt) = s

let drop_parens (s,x,nt) = 
  match nt with
    | Plain ->
        (s,x,Plain)
    | Paren(s1,s2) ->
        (Ast.combine_lex_skips s1 (Ast.combine_lex_skips s s2),x,Plain)
    | Bquote -> 
        assert false

let add_parens (s,x,nt) = 
  match nt with
    | Plain ->
        (None,x,Paren(s,None))
    | Paren(s1,s2) ->
        (s,x,Paren(s1,s2))
    | Bquote -> 
        assert false

let lskip_pp ppf (s,x,nt) = 
  match nt with
    | Plain -> 
        Format.fprintf ppf "%a%a" 
          Ast.pp_lex_skips s
          pp (from_rope x)
    | Paren _ -> 
        Format.fprintf ppf "%a(%a)" 
          Ast.pp_lex_skips s
          pp (from_rope x)
    | Bquote -> 
        Format.fprintf ppf "%a`%a`" 
          Ast.pp_lex_skips s 
          pp (from_rope x)

let lskip_rename f (s,x,nt) =
  (s,f x,nt)

let replace_lskip (s,x,nt) s_new = 
  match nt with
    | Plain | Bquote -> (s_new,x,nt)
    | Paren(s1,s2) -> (s,x,Paren(s_new,s2))

let get_prec gp (s,x,nt) =
  gp (Precedence.Op (Ulib.Text.to_string x))
