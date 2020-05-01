open Cerb_frontend
open Colour
open PPrint


(* ugly *)
let nocolour f x = 
  let before = !Colour.do_colour in
  Colour.do_colour := false;
  let pp = f x in
  Colour.do_colour := before;
  pp

let pps = Pp_utils.to_plain_pretty_string

let eq = equals
let ne = langle ^^ rangle
let lt = langle
let gt = rangle
let le = langle ^^ equals
let ge = rangle ^^ equals
let arrow = minus ^^ rangle


let (^^^) = Pp_prelude.(^^^)
let lines l = align (PPrint.separate (break 1) l)


let bold = pp_ansi_format [Bold]
let underline c s = string s ^/^ repeat (String.length s) (char c)

let h1 s = pp_ansi_format [Bold;Magenta] (break 1 ^^ break 1 ^^ underline '=' s)
let red_h1 s = pp_ansi_format [Bold;Red] (break 1 ^^ break 1 ^^ underline '=' s)
let h2 s = bold (break 1 ^^ underline '-' s)

let good = pp_ansi_format [Green]
let bad = pp_ansi_format [Red]


let typ n typ = n ^^ colon ^^^ typ

let inline_item item content = 
  (pp_ansi_format [Bold] item) ^^ colon ^^
  space ^^ content

let item item content = 
  (pp_ansi_format [Bold] item) ^^ colon ^^ space ^^ align (content)



let print pp = Cerb_backend.Pipeline.run_pp None (pp ^^ hardline)

let print_for_level debug_level print_level pp =
  if debug_level >= print_level then print pp else ()
    


let pp_expr e = nocolour Pp_mucore.Basic.pp_expr e
let pp_pexpr e = nocolour Pp_mucore.Basic.pp_pexpr e
