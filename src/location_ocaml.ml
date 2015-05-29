type t =
  | Loc_unknown
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * Lexing.position option

let unknown =
  Loc_unknown
