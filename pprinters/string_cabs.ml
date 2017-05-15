open Pp_cabs

let string_of_cabs_type_specifier tspec =
  Pp_utils.to_plain_string (pp_cabs_type_specifier tspec)
