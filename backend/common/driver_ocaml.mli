open Cerb_frontend

type driver_conf = {
(* TODO: bring back ==> [`Interactive | `Exhaustive | `Random] -> *)
  exec_mode: Global_ocaml.execution_mode;
  concurrency: bool;
  fs_dump: bool;
  trace: bool;
}

type execution_result = (Core.value list, Errors.error) Exception.exceptM

type batch_exit =
  | Unspecified of Ctype.ctype
  | Specified of Z.t
  | OtherValue of Core.value

type batch_output =
  | Defined of { exit: batch_exit; stdout: string; stderr: string; blocked: bool }
  | Undefined of { ub: Undefined.undefined_behaviour; stderr: string; loc: Location_ocaml.t }
  | Error of { msg: string; stderr: string }

val string_of_batch_exit: batch_exit -> string
val string_of_batch_output: ?json:bool -> ?is_charon:bool -> int option -> (string list * batch_output) -> string

val batch_drive:
  'a Core.file -> string list -> Sibylfs.fs_state -> driver_conf -> (string list * batch_output) list

val drive:
  'a Core.file -> string list -> Sibylfs.fs_state -> driver_conf -> execution_result
