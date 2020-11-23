module StringSet = Set.Make(String)

type t = Location_ocaml.t

type loc = t

type path = t OneList.t

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


let update (loc : t) (loc2 : Location_ocaml.t) = 
  if good_location loc2 then loc2 else loc


let log (locs : path) (loc' : Location_ocaml.t) : path =
  let open OneList in
  if good_location loc' then (loc' :: locs) else locs


let head_pos_of_location = 
  Location_ocaml.head_pos_of_location


let unpack l = l


let one locs = OneList.head locs
