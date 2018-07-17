type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers



val get_switches: unit -> cerb_switch list
val has_switch: cerb_switch -> bool
val set: string list -> unit
