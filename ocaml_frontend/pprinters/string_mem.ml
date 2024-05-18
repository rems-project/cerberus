let string_pretty_of_integer_value ival =
  Pp_utils.to_plain_string Impl_mem.(pp_pretty_integer_value ~basis:`Decimal ~use_upper:false ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := false;
    let ret = Impl_mem.pp_mem_value mval in
    Cerb_colour.do_colour := saved;
    ret
  end

let string_pretty_of_mem_value ?basis ~use_upper mval =
  Pp_utils.to_plain_string (Impl_mem.pp_pretty_mem_value ?basis ~use_upper mval)


let string_pretty_of_mem_value_decimal mval =
  string_pretty_of_mem_value ~basis:`Decimal ~use_upper:false mval



let string_of_pointer_value is_verbose ptr_val =
  Pp_utils.to_plain_string (Impl_mem.pp_pointer_value ~is_verbose:false ptr_val)


let string_of_iv_memory_constraint cs =
  Pp_utils.to_plain_string (Pp_mem.pp_mem_constraint (Impl_mem.pp_pretty_integer_value ~basis:`Decimal ~use_upper:false) cs)
