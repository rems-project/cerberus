open Defacto_memory_types
type assertions

val initial_assertions: unit -> assertions

val is_unsat: assertions -> bool
val check: mem_constraint -> assertions -> bool option
val add_mem_constraint: mem_constraint -> assertions -> assertions

val declare_address: address -> assertions -> assertions
