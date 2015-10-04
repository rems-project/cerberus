type assertions

val initial_assertions: unit -> assertions

val is_unsat: assertions -> bool
val check: Defacto_memory_types.mem_constraint -> assertions -> bool option
val add_mem_constraint: Defacto_memory_types.mem_constraint -> assertions -> assertions
