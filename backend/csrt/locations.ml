open PPrint
include Location_ocaml

let pp loc = Location_ocaml.pp_location loc

let withloc loc p : PPrint.document = 
  flow (break 1) [pp loc;p]
