type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers
  
    (* n=0 => basic proposal, other versions supported for now: n= 1, 4 *)
  | SW_no_integer_provenance of int


val get_switches: unit -> cerb_switch list
val has_switch: cerb_switch -> bool
val has_switch_pred: (cerb_switch -> bool) -> cerb_switch option
val set: string list -> unit
