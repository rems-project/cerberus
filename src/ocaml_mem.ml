open Memory_model

let () = print_endline "loading Ocaml_mem";;


module Mem = (
  val match !Prelude.mem_switch with
    | MemSymbolic -> (module Ocaml_defacto : Memory_model.Memory)
    | MemConcrete -> (module Concrete : Memory_model.Memory)
)

include Mem


let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)



let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Colour.do_colour in
    Colour.do_colour := false;
    let ret = pp_mem_value mval in
    Colour.do_colour := saved;
    ret
  end
