open Memory_model

module Mem = (
  val match !Prelude.mem_switch with
(*    | `MemSymbolic -> (module Ocaml_defacto : Memory_model.Memory)*)
    | `MemConcrete -> (module Concrete : Memory_model.Memory)
(*    | `MemTwin -> (module Twin : Memory_model.Memory) (* TODO *)
    | `MemCpp -> failwith "miserably"*)
)

include Mem


(* TODO: debug wrappers *)
let load loc ty ptrval =
  Debug_ocaml.print_debug 3 [] (fun () ->
    "ENTERING LOAD: ty=" ^ String_core_ctype.string_of_ctype ty ^
    ", ptr= " ^ Pp_utils.to_plain_string (Mem.pp_pointer_value ptrval)
  );
  Mem.bind
    (Mem.load loc ty ptrval) begin fun (fp, mval) ->
      Debug_ocaml.print_debug 3 [] (fun () ->
        "EXITING LOAD: mval := " ^ Pp_utils.to_plain_string (Mem.pp_mem_value mval)
      );
      Mem.return (fp, mval)
    end


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
