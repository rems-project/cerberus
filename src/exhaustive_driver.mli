type execution_result = (Core.pexpr list, Errors.error) Exception.exceptM

val drive: Symbol.sym UniqueId.supply -> unit Core.file -> string list -> bool -> execution_result
