open Pp_mem

let string_pretty_of_integer_value ival =
  Pp_utils.to_plain_string (pp_pretty_integer_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string (pp_mem_value mval)

let string_pretty_of_mem_value format mval =
  Pp_utils.to_plain_string (pp_pretty_mem_value format mval)


let string_pretty_of_mem_value_decimal mval =
  string_pretty_of_mem_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } mval



let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (pp_pointer_value ptr_val)
