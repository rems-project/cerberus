type t =
  | Loc_unknown
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * Lexing.position option

let unknown =
  Loc_unknown

let point pos =
  Loc_point pos


(* [with_cursor_from loc1 loc2] makes a new (region location) with the region from loc1 and the cursor (if any) from loc2 *)
let with_cursor_from loc1 loc2 =
  let cursor_opt = match loc2 with
    | Loc_unknown ->
        None
    | Loc_point z ->
        Some z
    | Loc_region (_, _, z) ->
        z in
  match loc1 with
    | Loc_unknown ->
        Loc_unknown
    | Loc_point z ->
        Loc_region (z, z, cursor_opt)
    | Loc_region (begin_loc, end_loc, _) ->
        Loc_region (begin_loc, end_loc, cursor_opt)
