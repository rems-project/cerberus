open Pp_core_ctype


let string_of_ctype ty =
  Pp_utils.to_plain_string (pp_ctype ty)
