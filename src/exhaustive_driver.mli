type driver_conf = {
(* TODO: bring back ==> [`Interactive | `Exhaustive | `Random] -> *)
  exec_mode: Smt2.execution_mode;
  concurrency: bool;
  experimental_unseq: bool;
}

type execution_result = (Core.value list, Errors.error) Exception.exceptM


val batch_drive:
  Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> driver_conf -> string list

val drive:
  Symbol.sym UniqueId.supply -> 'a Core.file -> string list -> driver_conf -> execution_result
