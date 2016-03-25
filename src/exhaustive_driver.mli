type execution_result = (Core.pexpr list, Errors.t6) Exception.exceptM

val drive: Symbol.sym UniqueId.supply -> unit Core.file -> string list -> bool -> execution_result
