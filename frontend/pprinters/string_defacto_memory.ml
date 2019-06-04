open Pp_defacto_memory

let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (pp_pointer_value ptr_val)

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string (pp_mem_value mval)

let string_pretty_of_mem_value basis_opt mval =
  Pp_utils.to_plain_string (pp_pretty_mem_value basis_opt mval)


let string_of_iv_memory_constraint cs =
  let format = { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } in
  Pp_utils.to_plain_string (Pp_mem.pp_mem_constraint (Pp_defacto_memory.pp_pretty_integer_value format) cs)



(* FOR DEBUG *)
let string_of_shift_path sh =
  Pp_utils.to_plain_string (pp_shift_path sh)
