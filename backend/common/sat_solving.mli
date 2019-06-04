open Defacto_memory_types2
type assertions

val initial_assertions: unit -> assertions

val is_unsat: assertions -> bool
val check: impl_mem_constraint -> assertions -> bool option
val add_mem_constraint: impl_mem_constraint -> assertions -> assertions

val declare_address: address -> assertions -> assertions
