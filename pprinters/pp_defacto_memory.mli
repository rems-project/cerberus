open Defacto_memory_types

val pp_pointer_value: impl_pointer_value -> PPrint.document
val pp_integer_value: impl_integer_value -> PPrint.document
val pp_integer_value_for_core: impl_integer_value -> PPrint.document
val pp_mem_value: impl_mem_value -> PPrint.document
val pp_mem_constraint: mem_constraint -> PPrint.document
val pp_mem_constraint2: impl_mem_constraint2 -> PPrint.document

val pp_pretty_pointer_value: impl_pointer_value -> PPrint.document
val pp_pretty_integer_value: Boot_printf.formatting -> impl_integer_value -> PPrint.document
val pp_pretty_mem_value: Boot_printf.formatting -> impl_mem_value -> PPrint.document


(* FOR DEBUG *)
val pp_shift_path: shift_path -> PPrint.document
