module StringSet = Set.Make(String)

type t = Location_ocaml.t

type loc = t

type path = t List1.t

let unknown = Location_ocaml.unknown

let is_unknown loc = loc = unknown


let pp loc = Location_ocaml.pp_location ~clever:false loc



let dirs_to_ignore = 
  StringSet.of_list 
    (List.map Cerb_runtime.in_runtime
       [ "libc/include"
       ; "libcore" 
       ; ("impls/" ^ Setup.impl_name ^ ".impl")
       ]
    )

let good_location (loc : Location_ocaml.t) = 
  if !Debug_ocaml.debug_level > 0 then true else
    match Location_ocaml.get_filename loc with
    | None -> false
    | Some file -> not (StringSet.mem (Filename.dirname file) dirs_to_ignore)


let updateB (loc : t) (loc2 : Location_ocaml.t) = 
  if good_location loc2 then (loc2, true) else (loc, false)

let update (loc : t) (loc2 : Location_ocaml.t) = 
  if good_location loc2 then loc2 
  else loc


let log (locs : path) (loc' : Location_ocaml.t) : path =
  if good_location loc' then List1.cons loc' locs else locs


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
    | Loc_region (startp, endp, ocursorp) ->
       let startp' = json_lexing_position startp in
       let endp' = json_lexing_position endp in
       let cursorp' = match ocursorp with
         | Some cursorp -> json_lexing_position cursorp
         | None -> `Null
       in
       let args = 
         [("region_start", startp');
          ("region_end", endp');
          ("region_cursor", cursorp')]
       in
       `Variant ("Region", Some (`Assoc args))
    | Loc_regions (starts_ends,ocursorp) ->
       let starts_ends' = 
         List.map (fun (startp, endp) ->
             let startp' = json_lexing_position startp in
             let endp' = json_lexing_position endp in
             `Assoc [("regions_start", startp'); ("regions_end", endp')]
           ) starts_ends
       in
       let cursorp' = match ocursorp with
         | Some cursorp -> json_lexing_position cursorp
         | None -> `Null
       in
       let args = 
         [("regions", `List starts_ends');
          ("cursor", cursorp')]
       in
       `Variant ("Region", Some (`Assoc args))
  in
  `Variant ("Loc", Some json)

let json_loc loc : Yojson.Safe.t =
  json_raw_loc (Location_ocaml.to_raw loc)


let json_path locs : Yojson.Safe.t = 
  let locs_json = List.map json_loc (List.rev (List1.to_list locs)) in
  `Variant ("path", Some (`List locs_json))
