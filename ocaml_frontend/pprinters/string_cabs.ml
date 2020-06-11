open Pp_cabs

(*
let string_of_cabs_type_specifier tspec =
  Pp_utils.to_plain_string (pp_cabs_type_specifier tspec)
*)

let string_of_declarator decltor =
  "Pp_utils.to_plain_string (pp_declarator decltor)"

let string_of_pointer_declarator decltor =
  "Pp_utils.to_plain_string (pp_pointer_declarator decltor)"
