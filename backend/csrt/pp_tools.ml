open Utils
open Cerb_frontend
open Colour
open PPrint


let (^^^) = Pp_prelude.(^^^)
let words l = PPrint.separate space l
let lines l = PPrint.separate (break 1) l

let eq = equals
let ne = langle ^^ rangle
let lt = langle
let gt = rangle
let le = langle ^^ equals
let ge = rangle ^^ equals
let arrow = minus ^^ rangle


let pps = Pp_utils.to_plain_pretty_string

let nocolour f x = 
  let before = !Colour.do_colour in
  Colour.do_colour := false;
  let pp = f x in
  Colour.do_colour := before;
  pp

let underline c s = string s ^/^ repeat (String.length s) (char c)
let h1 s = pp_ansi_format [Bold; Blue] (break 1 ^^ break 1 ^^ break 1 ^^ underline '=' s)
let h2 s = pp_ansi_format [Bold; Blue] (break 1 ^^ break 1 ^^ underline '=' s)


let typ n typ = n ^^ colon ^^^ typ
let alrctyp alrc n typ = (char alrc) ^^^ n ^^ colon ^^^ typ


let item item content = 
  (pp_ansi_format [Bold; Magenta] item) ^^ colon ^^ break 1 ^^
  space ^^ space ^^ space ^^ space ^^ space ^^ align content



let debug_print_for_level debug_level l =
  match filter_map (fun (l,s) -> if debug_level >= l then Some s else None) l with
  | [] -> ()
  | l -> Cerb_backend.Pipeline.run_pp None (lines l ^^ hardline)
    


let pp_expr e = nocolour Pp_mucore.Basic.pp_expr e
let pp_pexpr e = nocolour Pp_mucore.Basic.pp_pexpr e
