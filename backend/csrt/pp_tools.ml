open Cerb_frontend
open Colour
open PPrint



let debug_level = ref 0




let pp_num n = !^(Nat_big_num.to_string n)

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

let h1 s = bold (break 1 ^^ break 1 ^^ underline '=' s ^^ break 1 ^^ break 1)
let h2 s = bold (break 1 ^^ underline '-' s ^^ break 1)

let action a = 
  fancystring (ansi_format [Bold;Magenta] " * ") 3 ^^ !^a ^^ !^"..."

let greenb = ansi_format [Bold;Green]
let redb = ansi_format [Bold;Red]
let yellowb = ansi_format [Bold;Yellow]


let pp_env_list optional_wrapper l f = 
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



let print pp = Cerb_backend.Pipeline.run_pp None (pp ^^ hardline)


let debug_print print_level pp =
  if !debug_level >= print_level then print pp else ()
    


let pp_expr e = nocolour Pp_mucore.Basic.pp_expr e
let pp_pexpr e = nocolour Pp_mucore.Basic.pp_pexpr e



let warn pp = 
  print (hardline ^^ blank 3 ^^ 
           !^(yellowb "[!] Warning:") ^^^ pp ^^ 
             hardline ^^ hardline )

let error pp = 
  print empty;
  print empty;
  print (!^(redb "[!] Error") ^/^ pp);
  exit 1
