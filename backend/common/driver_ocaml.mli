open Cerb_frontend

type execution_result = (Core.value list, Errors.error) Exception.exceptM

type batch_exit =
  | Unspecified of Ctype.ctype
  | Specified of Z.t
  | OtherValue of Core.value

type batch_output =
  | Defined of { exit: batch_exit; stdout: string; stderr: string; blocked: bool }
  | Undefined of { ub: Undefined.undefined_behaviour; stderr: string; loc: Cerb_location.t }
  | Error of { msg: string; stderr: string }

val string_of_batch_exit: batch_exit -> string
val string_of_batch_output: ?json:bool -> ?is_charon:bool -> int option -> (string list * batch_output) -> string

val batch_drive:
  conf:Config.config -> 'a Core.file -> string list -> Sibylfs.fs_state -> (string list * batch_output) list

val drive:
  conf:Config.config -> 'a Core.file -> string list -> Sibylfs.fs_state -> execution_result
