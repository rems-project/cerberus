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


type ansi_format = ansi_style list

val ansi_format: ansi_format -> string -> string

val pp_ansi_format: ansi_format -> string -> PPrint.document
