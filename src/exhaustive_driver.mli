type execution_result = (Core_run_aux.core_run_annotation Core.expr list, Errors.t9) Exception.t3

val drive: Symbol.t2 UniqueId.supply -> unit Core.file -> string list -> bool -> execution_result
