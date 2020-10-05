include Location_ocaml

module CF = Cerb_frontend


let pp loc = Location_ocaml.pp_location loc

let precise loc mlock = 
  match mlock with
  | Some loc2 -> loc2
  | None -> loc


let update loc annots =
  precise loc (CF.Annot.get_loc annots)
