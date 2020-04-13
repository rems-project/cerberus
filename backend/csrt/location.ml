include Location_ocaml

let pp loc = 
  Cerb_frontend.Pp_utils.to_plain_string (Location_ocaml.pp_location loc)
