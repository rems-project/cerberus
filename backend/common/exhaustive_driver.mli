open Cerb_frontend

type driver_conf = {
(* TODO: bring back ==> [`Interactive | `Exhaustive | `Random] -> *)
  exec_mode: Global_ocaml.execution_mode;
  concurrency: bool;
  experimental_unseq: bool;
  fs_dump: bool;
  trace: bool;
}

type execution_result = (Core.value list, Errors.error) Exception.exceptM

val batch_drive:
  [`Batch | `CharonBatch] -> 'a Core.file -> string list -> Sibylfs.fs_state -> driver_conf -> string list

val drive:
  'a Core.file -> string list -> Sibylfs.fs_state -> driver_conf -> execution_result
