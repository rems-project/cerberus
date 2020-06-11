let string_pretty_of_integer_value ival =
  Pp_utils.to_plain_string (Impl_mem.pp_pretty_integer_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Colour.do_colour in
    Colour.do_colour := false;
    let ret = Impl_mem.pp_mem_value mval in
    Colour.do_colour := saved;
    ret
  end

let string_pretty_of_mem_value format mval =
  Pp_utils.to_plain_string (Impl_mem.pp_pretty_mem_value format mval)


let string_pretty_of_mem_value_decimal mval =
  string_pretty_of_mem_value { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } mval



let string_of_pointer_value ptr_val =
  Pp_utils.to_plain_string (Impl_mem.pp_pointer_value ptr_val)


let string_of_iv_memory_constraint cs =
  let format = { Boot_printf.basis= Some AilSyntax.Decimal; Boot_printf.use_upper= false } in
  Pp_utils.to_plain_string (Pp_mem.pp_mem_constraint (Impl_mem.pp_pretty_integer_value format) cs)
