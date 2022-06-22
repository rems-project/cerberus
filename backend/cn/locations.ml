(* taking things from ocaml_locations *)

module StringSet = Set.Make(String)

type t = Location_ocaml.t

type loc = t

type info = loc * string option

type path = t list

let unknown = Location_ocaml.unknown

let is_unknown_location = Location_ocaml.is_unknown_location


let pp loc = Location_ocaml.pp_location ~clever:false loc

let to_string loc = Location_ocaml.location_to_string loc

let other str = Location_ocaml.other str


let dirs_to_ignore = 
  StringSet.of_list 
    (List.map Cerb_runtime.in_runtime
       [ "libc/include"
       ; "libcore" 
       ; ("impls/" ^ Setup.impl_name ^ ".impl")
       ]
    )

let good_location (loc : Location_ocaml.t) = 
  match Location_ocaml.get_filename loc, Location_ocaml.is_other loc with
  | Some file, _ -> not (StringSet.mem (Filename.dirname file) dirs_to_ignore)
  | _, Some other -> true
  | None, _ -> false


let updateB (loc : t) (loc2 : Location_ocaml.t) = 
  if good_location loc2 then (loc2, true) 
  else (loc, false)

let update (loc : t) (loc2 : Location_ocaml.t) = 
  if good_location loc2 then loc2 
  else loc


let log (locs : path) (loc' : Location_ocaml.t) : path =
  if good_location loc' then loc' :: locs else locs


let head_pos_of_location = 
  Location_ocaml.head_pos_of_location


let unpack l = l


(* type position = {
 *   	pos_fname : string;
 *   	pos_lnum : int;
 *   	pos_bol : int;
 *   	pos_cnum : int;
 * } *)


let json_lexing_position p = 
  let open Lexing in
  `Assoc [("file", `String p.pos_fname);
          ("line", `Int p.pos_lnum);
          ("char", `Int (p.pos_cnum - p.pos_bol))]

let json_raw_loc loc : Yojson.Safe.t = 
  let open Location_ocaml in
  let json = match loc with
    | Loc_unknown -> 
       `Variant ("Unknown", None)
    | Loc_other str -> 
       `Variant ("Other", Some (`String str))
    | Loc_point point -> 
       `Variant ("Point", Some (json_lexing_position point))
      (* start, end, cursor *)
    | Loc_region (startp, endp, cursor) ->
       let startp' = json_lexing_position startp in
       let endp' = json_lexing_position endp in
       let cursor' = match cursor with
         | NoCursor ->
            `Variant ("NoCursor", None)
         | PointCursor p ->
            `Variant ("PointCursor", Some (json_lexing_position p))
         | RegionCursor (b ,e) ->
            `Variant ("RegionCursor", Some (`Assoc [ ("cursor_start", json_lexing_position b)
                                                   ; ("cursor_end", json_lexing_position e) ]))
         in
       let args = 
         [("region_start", startp');
          ("region_end", endp');
          ("region_cursor", cursor')]
       in
       `Variant ("Region", Some (`Assoc args))
    | Loc_regions (starts_ends,cursor) ->
       let starts_ends' = 
         List.map (fun (startp, endp) ->
             let startp' = json_lexing_position startp in
             let endp' = json_lexing_position endp in
             `Assoc [("regions_start", startp'); ("regions_end", endp')]
           ) starts_ends
       in
       let cursor' = match cursor with
         | NoCursor ->
            `Variant ("NoCursor", None)
         | PointCursor p ->
            `Variant ("PointCursor", Some (json_lexing_position p))
         | RegionCursor (b ,e) ->
            `Variant ("RegionCursor", Some (`Assoc [ ("cursor_start", json_lexing_position b)
                                                   ; ("cursor_end", json_lexing_position e) ]))
       in
       let args = 
         [("regions", `List starts_ends');
          ("cursor", cursor')]
       in
       `Variant ("Region", Some (`Assoc args))
  in
  json

let json_loc loc : Yojson.Safe.t =
  json_raw_loc (Location_ocaml.to_raw loc)


let json_path locs : Yojson.Safe.t = 
  let locs_json = List.map json_loc (List.rev locs) in
  `Variant ("path", Some (`List locs_json))




type region = Lexing.position * Lexing.position


let point = Location_ocaml.point
let region = Location_ocaml.region
let regions = Location_ocaml.regions



let simple_location = Location_ocaml.simple_location

let line_numbers = Location_ocaml.line_numbers

let is_region x = match Location_ocaml.to_raw x with
    | Location_ocaml.Loc_region (l, r, _) -> Some (l, r)
    | _ -> None


