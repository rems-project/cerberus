open Format
open Pp

(* These compare faster than BatRope.t *)
type t = BatUTF8.t
let compare r1 r2 = 
  BatUTF8.compare r1 r2

let from_rope r = BatRope.to_ustring r

let to_rope n = BatRope.of_ustring n
let to_string = BatUTF8.to_string

(*
type t = string
let compare r1 r2 = 
  Pervasives.compare r1 r2

let from_rope r = BatRope.to_string r

let to_rope n = BatRope.of_string n
let to_string n = n
 *)
  (*
type t = BatRope.t
let compare r1 r2 = 
  if r1 == r2 then 
    0 
  else 
    BatRope.compare r1 r2

let from_rope r = r

let to_rope n = n
let to_string n = BatRope.to_string n
   *)

let (^) = BatRope.(^^^)

let fresh_start start s ok =
  let rec f (n:int) =
    let name = s ^ BatRope.of_latin1 (BatInt.to_string n) in
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

let starts_with_upper_letter x = BatCamomile.UCharInfo.general_category (BatRope.get (to_rope x) 0) = `Lu

let starts_with_lower_letter x = BatCamomile.UCharInfo.general_category (BatRope.get (to_rope x) 0) = `Ll

let uncapitalize x = 
  assert (starts_with_upper_letter x);
  from_rope (BatRope.uncapitalize (to_rope x))

let capitalize x =
  assert (starts_with_lower_letter x);
  from_rope (BatRope.capitalize (to_rope x))

type name_type =
  | Bquote
  | Paren of Ast.lex_skips * Ast.lex_skips
  | Plain

type lskips_t = Ast.lex_skips * BatRope.t * name_type

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

let to_output_quoted a (s,x,nt)= 
  let open Output in
  let (^^) = BatRope.(^^^) in
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
    | Plain -> pp ppf (from_rope x)
    | Paren _ -> 
        Format.fprintf ppf "(%a)" pp (from_rope x)
    | Bquote -> 
        Format.fprintf ppf "`%a`" pp (from_rope x)

let lskip_rename f (s,x,nt) =
  (s,f x,nt)

let replace_lskip (s,x,nt) s_new = 
  match nt with
    | Plain | Bquote -> (s_new,x,nt)
    | Paren(s1,s2) -> (s,x,Paren(s_new,s2))

let get_prec gp (s,x,nt) =
  gp (Precedence.Op (BatRope.to_string x))
