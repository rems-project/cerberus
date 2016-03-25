open Defacto_memory_types

val pp_pointer_value: pointer_value -> PPrint.document
val pp_integer_value: integer_value -> PPrint.document
val pp_integer_value_for_core: integer_value -> PPrint.document
val pp_mem_value: mem_value -> PPrint.document
val pp_mem_constraint: mem_constraint -> PPrint.document

val pp_pretty_pointer_value: pointer_value -> PPrint.document
val pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document


(* FOR DEBUG *)
val pp_shift_path: shift_path -> PPrint.document
