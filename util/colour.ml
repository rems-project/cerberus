module P = PPrint
let (!^ ) = P.(!^)
let (^^)  = P.(^^)

(* Part of the escape ANSI's "Select Graphic Rendition" parameters *)
type ansi_style =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White
  | Bold
  | Underline
  | Blinking
  | Inverted
  (* TODO: the complete list *)

type ansi_format = ansi_style list

let int_fg = function
  | Black     -> 30
  | Red       -> 31
  | Green     -> 32
  | Yellow    -> 33
  | Blue      -> 34
  | Magenta   -> 35
  | Cyan      -> 36
  | White     -> 37
  | Bold      -> 1
  | Underline -> 4
  | Blinking  -> 5
  | Inverted  -> 7

(* TODO: yuck!!!! *)
let do_colour =
  ref (Unix.isatty Unix.stdout)

let without_colour f x =
  let col = ! do_colour in
  do_colour := false;
  let r = f x in
  do_colour := col;
  r

let ansi_format f str =
  if !do_colour then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    "\x1b[" ^ g f ^ str ^ "\x1b[0m"
  else
    str

let pp_ansi_format f mk_doc =
  let doc = without_colour mk_doc () in
  if !do_colour then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    !^ ("\x1b[" ^ g f) ^^ doc ^^ !^ "\x1b[0m"
  else
    doc
