open Cerb_frontend
open Colour
open Printf

let debug_level = 1

let pps = Pp_utils.to_plain_pretty_string

let nocolour f x = 
  let before = !Colour.do_colour in
  Colour.do_colour := false;
  let pp = f x in
  Colour.do_colour := before;
  pp

let pp_expr e = pps (nocolour Pp_mucore.Basic.pp_expr e)
let pp_pexpr e = pps (nocolour Pp_mucore.Basic.pp_pexpr e)

let lines s = (String.concat "\n" s)
let underline c s = s ^ "\n" ^ (String.make (String.length s) c)


let h1 s = ansi_format [Bold; Blue] (underline '=' s)
let h2 s = ansi_format [Bold; Blue] (underline '-' s)
let item item content = 
  sprintf "%s: %s" (ansi_format [Bold; Magenta] item) content


let debug_print_line level s = 
  if debug_level >= level then print_endline s else ()

let debug_print level s = 
  if debug_level >= level then print_endline ("\n" ^ lines s) else ()
