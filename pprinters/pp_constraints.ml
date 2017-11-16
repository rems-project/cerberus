open Constraints
let pp_old_constraints (Constraints xs) =
  let strs = List.map (fun z -> Pp_utils.to_plain_string (Pp_symbolic.pp_symbolic Pp_core.pp_object_value Pp_mem.pp_pointer_value z)) xs in
  "[" ^ String.concat ", " strs ^ "]"
