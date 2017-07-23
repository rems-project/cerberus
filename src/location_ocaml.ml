open Lexing

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


let location_to_string loc =
  let string_of_pos pos =
    Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol) in
  
  match loc with
    | Loc_unknown ->
        "unknown location"
    | Loc_point pos ->
        string_of_pos pos ^ ":"
    | Loc_region (pos1, pos2, _) ->
        (* TODO *)
        string_of_pos pos1 ^ "-" ^ string_of_pos pos2 ^ ":"
