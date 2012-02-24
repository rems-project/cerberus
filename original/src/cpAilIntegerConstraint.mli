(* Basic constraint set. *)
val set : CpAilConstraint.t

(* Limits *)
val char_bit : CpAilConstraint.constant

val char_min : CpAilConstraint.constant
val char_max : CpAilConstraint.constant
val schar_min : CpAilConstraint.constant
val schar_max : CpAilConstraint.constant
val uchar_max : CpAilConstraint.constant
val shrt_min : CpAilConstraint.constant
val shrt_max : CpAilConstraint.constant
val ushrt_max : CpAilConstraint.constant
val int_min : CpAilConstraint.constant
val int_max : CpAilConstraint.constant
val uint_max : CpAilConstraint.constant
val long_min : CpAilConstraint.constant
val long_max : CpAilConstraint.constant
val ulong_max : CpAilConstraint.constant
val llong_min : CpAilConstraint.constant
val llong_max : CpAilConstraint.constant
val ullong_max : CpAilConstraint.constant

val bool_size : CpAilConstraint.constant
val char_size : CpAilConstraint.constant
val schar_size : CpAilConstraint.constant
val uchar_size : CpAilConstraint.constant
val shrt_size : CpAilConstraint.constant
val ushrt_size : CpAilConstraint.constant
val int_size : CpAilConstraint.constant
val uint_size : CpAilConstraint.constant
val long_size : CpAilConstraint.constant
val ulong_size : CpAilConstraint.constant
val llong_size : CpAilConstraint.constant
val ullong_size : CpAilConstraint.constant

val bool_align : CpAilConstraint.constant
val char_align : CpAilConstraint.constant
val schar_align : CpAilConstraint.constant
val uchar_align : CpAilConstraint.constant
val shrt_align : CpAilConstraint.constant
val ushrt_align : CpAilConstraint.constant
val int_align : CpAilConstraint.constant
val uint_align : CpAilConstraint.constant
val long_align : CpAilConstraint.constant
val ulong_align : CpAilConstraint.constant
val llong_align : CpAilConstraint.constant
val ullong_align : CpAilConstraint.constant
