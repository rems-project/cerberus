type execution_result = (Core.pexpr list, Errors.error) Exception.exceptM

val batch_drive: Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> Global_ocaml.cerberus_conf -> unit
val drive: Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> Global_ocaml.cerberus_conf -> execution_result
