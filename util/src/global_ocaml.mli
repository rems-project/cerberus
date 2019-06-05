val (-|): ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type execution_mode =
  | Exhaustive
  | Random

type cerberus_conf = {
  exec_mode_opt:   execution_mode option;
  concurrency:     bool;
  error_verbosity: error_verbosity;
  defacto:         bool;
  n1570:           Yojson.Basic.json option;
}

(* print an error fatal message and exit with a given code (default is 1) *)
val error: ?code:int -> string -> 'a

val (!!): (unit -> 'a) ref -> 'a

val cerb_path: string

val cerb_conf: (unit -> cerberus_conf) ref

val set_cerb_conf:
    bool ->
    execution_mode ->
    bool ->
    error_verbosity ->
    bool ->
    bool ->
    unit

(* NOTE: used in driver.lem *)
val current_execution_mode: unit -> execution_mode option

val concurrency_mode: unit -> bool
val isDefacto: unit -> bool

(* NOTE: used in pp_errors.ml *)
val verbose: unit -> error_verbosity
val n1570: unit -> Yojson.Basic.json option

val error: ?code:int -> string -> 'a
