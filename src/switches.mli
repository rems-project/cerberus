type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads



val get_switches: unit -> cerb_switch list
val has_switch: cerb_switch -> bool
val set: string list -> unit
