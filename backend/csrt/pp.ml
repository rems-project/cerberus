module CF = Cerb_frontend
include PPrint

open Colour



let debug_level = ref 0


let plain = CF.Pp_utils.to_plain_pretty_string

let arrow = minus ^^ rangle

let (^^^) = Pp_prelude.(^^^)

let bold = pp_ansi_format [Bold]
let underline c s = string s ^/^ repeat (String.length s) (char c)

let h1 s = bold (break 1 ^^ break 1 ^^ underline '=' s ^^ break 1 ^^ break 1)
let h2 s = bold (break 1 ^^ underline '-' s ^^ break 1)

let action a = 
  fancystring (ansi_format [Bold;Magenta] " * ") 3 ^^ !^a ^^ !^"..."

let greenb = ansi_format [Bold;Green]
let redb = ansi_format [Bold;Red]
let yellowb = ansi_format [Bold;Yellow]


let pp_list optional_wrapper f l = 
  match l with
  | [] -> !^"(empty)"
  | l -> 
     let pp = flow_map (comma ^^ break 1) f l in
     match optional_wrapper with
     | Some wrapper -> wrapper pp
     | None -> pp


let typ n typ = n ^^ colon ^^^ typ

let inline_item item content = 
  fancystring (ansi_format [Bold] item) (String.length item) ^^ 
    colon ^^ space ^^ content

let item item content = 
  fancystring (ansi_format [Bold] item) (String.length item) ^^ 
    colon ^^ space ^^ align content




(* ugly *)
let nocolour f x = 
  let before = !Colour.do_colour in
  Colour.do_colour := false;
  let pp = f x in
  Colour.do_colour := before;
  pp


let pp_num n = !^(Nat_big_num.to_string n)

let pp_expr e = nocolour CF.Pp_mucore.Basic.pp_expr e
let pp_pexpr e = nocolour CF.Pp_mucore.Basic.pp_pexpr e

let pp_ctype = CF.Pp_core_ctype.pp_ctype











