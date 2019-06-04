(* Standard usage logging *)

let log =
  ref []


let init () =
  log := []


let log_standard str f =
  log := str :: !log;
  f

let get_log =
  !log
