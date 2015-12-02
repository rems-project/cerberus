open Mem
open Mem_common

val pp_pure_memop: pure_memop -> PPrint.document
val pp_memop: memop -> PPrint.document

(* val pp_pointer_shift: pointer_shift0 -> PPrint.document *)
val pp_pointer_value: pointer_value0 -> PPrint.document
val pp_integer_value: integer_value0 -> PPrint.document
val pp_mem_value: mem_value0 -> PPrint.document

val pp_pretty_pointer_value: pointer_value0 -> PPrint.document
val pp_pretty_mem_value: Boot_printf.formatting -> mem_value0 -> PPrint.document
