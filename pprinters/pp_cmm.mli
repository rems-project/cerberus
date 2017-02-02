val pp_constraints: Constraints.t4 -> string
val dot_of_pre_execution: Cmm_csem.pre_execution -> string -> string -> string
val dot_of_exeState: Cmm_op.symState -> string -> string -> string
val pp_execState: Cmm_op.symState -> string
val string_of_exeState: Cmm_op.symState -> string

val pp_constraints_symbolic: (Core.object_value, Mem.pointer_value) Symbolic.symbolic -> string
