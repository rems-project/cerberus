open Lexing

type t =
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * Lexing.position option

let unknown =
  Loc_unknown

let other str =
  Loc_other str

let point pos =
  Loc_point pos

let first = function
  | loc::_ -> loc
  | [] -> Loc_unknown

(* [with_cursor_from loc1 loc2] makes a new (region location) with the region from loc1 and the cursor (if any) from loc2 *)
let with_cursor_from loc1 loc2 =
  let cursor_opt = match loc2 with
    | Loc_unknown ->
        None
    | Loc_other _ ->
        None
    | Loc_point z ->
        Some z
    | Loc_region (_, _, z) ->
        z in
  match loc1 with
    | Loc_unknown ->
        Loc_unknown
    | Loc_other str ->
        Loc_other str
    | Loc_point z ->
        Loc_region (z, z, cursor_opt)
    | Loc_region (begin_loc, end_loc, _) ->
        Loc_region (begin_loc, end_loc, cursor_opt)

let from_main_file = function
  | Loc_unknown
  | Loc_other _ -> false
  | Loc_point pos
  | Loc_region (pos, _, _) ->
    let ext = Filename.extension pos.pos_fname in
    ext = ".c" || ext = ".core"

let outer_bbox xs =
 let (b0, e0) = match xs with
   | [] ->
       assert false
   | (b,e) :: _ ->
       (b,e) in
 let pos_lt pos1 pos2 =
   (* assuming pos_fname are the same *)
   if pos1.pos_lnum = pos2.pos_lnum then
     pos1.pos_cnum < pos2.pos_cnum
   else
     pos1.pos_lnum < pos2.pos_lnum in
 List.fold_left (fun (bAcc, eAcc) (b, e) ->
   ((if pos_lt b bAcc then b else bAcc), (if pos_lt e eAcc then eAcc else e))
 ) (b0, e0) xs

let bbox_location xs =
  let bound_opts = List.map (function
    | Loc_unknown
    | Loc_other _ ->
        None
    | Loc_point pos ->
        Some (pos, pos)
    | Loc_region (pos1, pos2, _) ->
        (* invariant from Loc_region is that pos1 <= pos2 *)
        Some (pos1, pos2)
  ) xs in
  let (b, e) = outer_bbox begin
    List.fold_left (fun acc opt ->
      match opt with
        | None ->
            acc
        | Some z ->
            z :: acc
    ) [] bound_opts
  end in
  Loc_region (b, e, None)

let location_to_string loc =
  let string_of_pos pos =
    Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol) in
  match loc with
    | Loc_unknown ->
        "unknown location"
    | Loc_other str ->
        "other_location(" ^ str ^ ")"
    | Loc_point pos ->
        string_of_pos pos ^ ":"
    | Loc_region (pos1, pos2, _) ->
        string_of_pos pos1 ^ "-" ^
        begin if pos1.pos_fname = pos2.pos_fname then
          ""
        else
          pos2.pos_fname
        end ^
        begin if pos1.pos_lnum = pos2.pos_lnum then
          ""
        else
          string_of_int pos2.pos_lnum
        end ^
        string_of_int (1+pos2.pos_cnum-pos2.pos_bol)
