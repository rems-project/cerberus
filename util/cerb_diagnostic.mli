exception Internal_error of string

(* prints the msg prefixed by "internal error:" and raise the
 * Internal_error exception *)
val internal_error: string -> 'a

(* prints the msg prefixed by "error:" and with a given code (default is 1) *)
val fatal: ?code:int -> string -> 'a

(* if the always is true or the debug level is >1, prints the msg
 * prefixed by "warning:" *)
val warn: ?always:bool -> Cerb_debug.domain list -> (unit -> string) -> unit