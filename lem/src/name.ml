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
  | Paren
  | Plain

type lskips_t = Ast.lex_skips * Ulib.Text.t * name_type

let from_ix = function 
  | Ast.SymX_l((s,x),l) -> (s,x,Plain)
  | Ast.InX_l(s,(None,x),None,l) -> (s,x,Bquote)
  | _ -> assert false

let from_x = function 
  | Ast.X_l((s,x),l) -> (s,x,Plain)
  | Ast.PreX_l(s1,(None,x),None,l) -> (s1,x,Paren)
  | Ast.PreX_l(s1,(_,x),_,l) -> 
      (* The parser should prevent this from happening in its mk_pre_x_l
       * function *)
      assert false


let strip_lskip (_,x,_) = from_rope x

let add_lskip n = 
  (None,to_rope n,Plain)

let star = Ulib.Text.of_latin1 "*"
let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])

let to_output a (s,x,nt)= 
  let open Output in
    match nt with
      | Plain -> ws s ^ id a x
      (* TODO : Parens might not be correct for all targets *)
      | Paren ->
          if (Ulib.Text.left x 1 = star || Ulib.Text.right x 1 = star) then
            ws s ^ kwd "(" ^ space ^ id a x ^ space ^ kwd ")"
          else
            ws s ^ kwd "(" ^ id a x ^ kwd ")"
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
      | Paren ->
          ws s ^ kwd "(" ^ id a (r"\"" ^^ x ^^ r"\"") ^ kwd ")"
      (* TODO : Bquote might not be correct for all targets *)
      | Bquote -> 
          ws s ^ kwd "`" ^ id a (r"\"" ^^ x ^^ r"\"") ^ kwd "`"

let to_rope_tex a n = 
  Output.to_rope_ident a (to_rope n)

let add_pre_lskip lskip (s,x,nt) = 
  (Ast.combine_lex_skips lskip s,x,nt)

let get_lskip (s,x,nt) = s

let drop_parens (s,x,nt) = 
  match nt with
    | Plain ->
        (s,x,Plain)
    | Paren ->
        (s,x,Plain)
    | Bquote -> 
        assert false

let add_parens (s,x,nt) = 
  match nt with
    | Plain ->
        (s,x,Paren)
    | Paren ->
        (s,x,Paren)
    | Bquote -> 
        assert false

let lskip_pp ppf (s,x,nt) = 
  match nt with
    | Plain -> 
        Format.fprintf ppf "%a%a" 
          Ast.pp_lex_skips s
          pp (from_rope x)
    | Paren -> 
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
  (s_new,x,nt)

let get_prec gp (s,x,nt) =
  gp (Precedence.Op (Ulib.Text.to_string x))
