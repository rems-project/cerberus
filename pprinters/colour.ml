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


let ansi_format f str =
  if Unix.isatty Unix.stdout then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    "\x1b[" ^ g f ^ str ^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    str


let pp_ansi_format f doc =
  if Unix.isatty Unix.stdout then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    !^ ("\x1b[" ^ g f) ^^ doc ^^ !^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    doc
