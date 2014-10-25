type t =
  Lexing.position * Lexing.position

let unknown =
  (Lexing.dummy_pos, Lexing.dummy_pos)
