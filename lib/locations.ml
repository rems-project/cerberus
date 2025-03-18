(* taking things from ocaml_locations *)

module StringSet = Set.Make (String)

type t = Cerb_location.t

type info = t * string option

type path = t list

let is_unknown_location = Cerb_location.is_unknown_location

let pp loc = Cerb_location.pp_location ~clever:false loc

let to_string loc = Cerb_location.location_to_string loc

let other str = Cerb_location.other str

let dirs_to_ignore =
  StringSet.of_list
    (List.map
       Cerb_runtime.in_runtime
       [ "libc/include"; "libcore"; "impls/" ^ Setup.impl_name ^ ".impl" ])


let good_location (loc : Cerb_location.t) =
  match (Cerb_location.get_filename loc, Cerb_location.is_other loc) with
  | Some file, _ -> not (StringSet.mem (Filename.dirname file) dirs_to_ignore)
  | _, Some _other -> true
  | None, _ -> false


let updateB (loc : t) (loc2 : Cerb_location.t) =
  if good_location loc2 then
    (loc2, true)
  else
    (loc, false)


let update (loc : t) (loc2 : Cerb_location.t) =
  if good_location loc2 then
    loc2
  else
    loc


let log (locs : path) (loc' : Cerb_location.t) : path =
  if good_location loc' then loc' :: locs else locs


let head_pos_of_location = Cerb_location.head_pos_of_location

let unpack l = l

(* type position = {
 *      pos_fname : string;
 *      pos_lnum : int;
 *      pos_bol : int;
 *      pos_cnum : int;
 * } *)

let json_lexing_position p =
  let open Lexing in
  `Assoc
    [ ("file", `String p.pos_fname);
      ("line", `Int p.pos_lnum);
      ("char", `Int (p.pos_cnum - p.pos_bol))
    ]


let json_raw_loc loc : Yojson.Safe.t =
  let open Cerb_location in
  let json =
    match loc with
    | Loc_unknown -> `Variant ("Unknown", None)
    | Loc_other str -> `Variant ("Other", Some (`String str))
    | Loc_point point ->
      `Variant ("Point", Some (json_lexing_position point)) (* start, end, cursor *)
    | Loc_region (startp, endp, cursor) ->
      let startp' = json_lexing_position startp in
      let endp' = json_lexing_position endp in
      let cursor' =
        match cursor with
        | NoCursor -> `Variant ("NoCursor", None)
        | PointCursor p -> `Variant ("PointCursor", Some (json_lexing_position p))
        | RegionCursor (b, e) ->
          `Variant
            ( "RegionCursor",
              Some
                (`Assoc
                  [ ("cursor_start", json_lexing_position b);
                    ("cursor_end", json_lexing_position e)
                  ]) )
      in
      let args =
        [ ("region_start", startp'); ("region_end", endp'); ("region_cursor", cursor') ]
      in
      `Variant ("Region", Some (`Assoc args))
    | Loc_regions (starts_ends, cursor) ->
      let starts_ends' =
        List.map
          (fun (startp, endp) ->
            let startp' = json_lexing_position startp in
            let endp' = json_lexing_position endp in
            `Assoc [ ("regions_start", startp'); ("regions_end", endp') ])
          starts_ends
      in
      let cursor' =
        match cursor with
        | NoCursor -> `Variant ("NoCursor", None)
        | PointCursor p -> `Variant ("PointCursor", Some (json_lexing_position p))
        | RegionCursor (b, e) ->
          `Variant
            ( "RegionCursor",
              Some
                (`Assoc
                  [ ("cursor_start", json_lexing_position b);
                    ("cursor_end", json_lexing_position e)
                  ]) )
      in
      let args = [ ("regions", `List starts_ends'); ("cursor", cursor') ] in
      `Variant ("Region", Some (`Assoc args))
  in
  json


let json_loc loc : Yojson.Safe.t = json_raw_loc loc

let json_path locs : Yojson.Safe.t =
  let locs_json = List.map json_loc (List.rev locs) in
  `Variant ("path", Some (`List locs_json))


type region = Lexing.position * Lexing.position

let point = Cerb_location.point

let region = Cerb_location.region

let regions = Cerb_location.regions

let simple_location = Cerb_location.simple_location

let line_numbers = Cerb_location.line_numbers

let is_region = function Cerb_location.Loc_region (l, r, _) -> Some (l, r) | _ -> None

let start_pos = function
  | Cerb_location.Loc_point loc | Loc_region (loc, _, _) | Loc_regions ((loc, _) :: _, _)
    ->
    Some loc
  | _ -> None


let end_pos = function
  | Cerb_location.Loc_point loc | Loc_region (_, loc, _) -> Some loc
  | Loc_regions (list, _) ->
    (* can't use Option module without a cyclic dependency? *)
    (match List.last list with None -> None | Some (_, loc) -> Some loc)
  | _ -> None


let get_region = function
  | Cerb_location.Loc_region (start, end_, cursor) -> Some (start, end_, cursor)
  | _ -> None
