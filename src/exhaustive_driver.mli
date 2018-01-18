type driver_conf = {
  concurrency: bool;
  experimental_unseq: bool;
}

type execution_result = (Core.value list, Errors.error) Exception.exceptM


val batch_drive:
  Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> driver_conf -> unit

val drive:
  Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> driver_conf -> execution_result
