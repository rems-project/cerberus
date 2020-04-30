open PPrint
include Location_ocaml

let pp loc = Location_ocaml.pp_location loc

let withloc loc p : PPrint.document = 
  pp loc ^^ dot ^^ space ^^ p
