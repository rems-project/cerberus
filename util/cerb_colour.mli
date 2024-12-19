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

val do_colour: bool ref
val with_colour: ('a -> 'b) -> 'a -> 'b
val without_colour: ('a -> 'b) -> 'a -> 'b
val ansi_format: ?err:bool -> ansi_format -> string -> string
val pp_ansi_format: ?err:bool -> ansi_format -> (unit -> PPrint.document) -> PPrint.document
