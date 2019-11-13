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

let do_colour_stderr =
  ref (Unix.isatty Unix.stderr)

let ansi_format ?(err=false) f str =
  if !do_colour && (if err then !do_colour_stderr else true) then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    "\x1b[" ^ g f ^ str ^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    str


let pp_ansi_format ?(err=false) f doc =
  if !do_colour && (if err then !do_colour_stderr else true) then
    let g f = String.concat ";" (List.map (fun z -> string_of_int (int_fg z)) f) ^ "m" in
    !^ ("\x1b[" ^ g f) ^^ doc ^^ !^ "\x1b[0m" (* TODO: optimize, someday *)
  else
    doc
