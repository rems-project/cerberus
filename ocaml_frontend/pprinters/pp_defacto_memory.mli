open Defacto_memory_types

val pp_pointer_value: ?is_verbose:bool -> impl_pointer_value -> PPrint.document
val pp_integer_value: impl_integer_value -> PPrint.document
val pp_integer_value_for_core: impl_integer_value -> PPrint.document
val pp_mem_value: impl_mem_value -> PPrint.document

val pp_pretty_pointer_value: impl_pointer_value -> PPrint.document
val pp_pretty_integer_value: ?basis:Memory_model.basis -> use_upper:bool -> impl_integer_value -> PPrint.document
val pp_pretty_mem_value: ?basis:Memory_model.basis -> use_upper:bool -> impl_mem_value -> PPrint.document


(* FOR DEBUG *)
val pp_shift_path: shift_path -> PPrint.document
