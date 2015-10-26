open Pp_mem

let string_of_mem_value mval =
  Pp_utils.to_plain_string (pp_mem_value mval)

let string_pretty_of_mem_value format mval =
  Pp_utils.to_plain_string (pp_pretty_mem_value format mval)


let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (pp_pointer_value ptr_val)
