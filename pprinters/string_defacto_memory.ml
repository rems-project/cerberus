open Pp_defacto_memory

let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (pp_pointer_value ptr_val)

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string (pp_mem_value mval)

let string_pretty_of_mem_value basis_opt mval =
  Pp_utils.to_plain_string (pp_pretty_mem_value basis_opt mval)

(* FOR DEBUG *)
let string_of_shift_path sh =
  Pp_utils.to_plain_string (pp_shift_path sh)
