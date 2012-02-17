module type LOGGER = sig
  val log : CpMessage.t -> unit
end

module StdOut = struct
  module M = CpMessage

  let level_to_string msg =
    match M.level msg with
    | M.BUG -> "BUG"
    | M.ERROR -> "ERROR"
    | M.WARNING -> "WARNING"
    | M.INFO -> "INFO"
    | M.DEBUG -> "DEBUG"

  let log msg =
    let msg_string = M.to_string msg in
    let lvl_string = level_to_string msg in
    BatPrintf.printf "[%s] %s\n" lvl_string msg_string;
    match M.level msg with
    | M.BUG | M.ERROR ->
        Pervasives.exit 1
    | _ -> ()
end

module M = CpMessage

let l = ref (module StdOut : LOGGER)
let set logger = (l := logger)

let log msg =
  let module L = (val !l : LOGGER) in
  L.log msg

let bug f m = log (M.bug f m)
let error f m = log (M.error f m)
let warning f m = log (M.warning f m)
let info f m = log (M.info f m)
let debug f m = log (M.debug f m)
