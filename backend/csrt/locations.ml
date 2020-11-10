module StringSet = Set.Make(String)

type t = Location_ocaml.t

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

let update (loc : t) (loc2 : Location_ocaml.t) = 
  if !Debug_ocaml.debug_level > 0 then loc2 else
  match Location_ocaml.get_filename loc2 with
  | None -> loc
  | Some filename ->
     let dir = Filename.dirname filename in
     if StringSet.mem dir dirs_to_ignore
     then loc else loc2


let update_a loc annots =
  update loc (Cerb_frontend.Annot.get_loc_ annots)


let head_pos_of_location = 
  Location_ocaml.head_pos_of_location


let unpack l = l
