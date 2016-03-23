type execution_result = (Core.pexpr list, Errors.t5) Exception.t2

val drive: Symbol.sym UniqueId.supply -> unit Core.file -> string list -> bool -> execution_result
