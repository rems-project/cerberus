type cerb_switch =
  (* `PERMISSIVE allows out-of-bound pointer values. This the default behaviour
     for PNVI, whereas `STRICT (making out-of-bound pointer values creations
     UB, as in ISO) is the default for all variant of PNVI *)
  | SW_pointer_arith of [ `PERMISSIVE | `STRICT ]
  
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads
  
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers
  
    (* make the equality operators strictly base on the numerical value of pointers *)
  | SW_strict_pointer_equality
  
    (* make the relational operators UB when relating distinct objects (ISO) *)
  | SW_strict_pointer_relationals
  
  | SW_PNVI of [ `PLAIN | `AE | `AE_UDI ]
  | SW_CHERI

    (* the elaboration places the allocation/initialisation/deallocation of
       non-variadic functions inside the body of the Core procedures
       (instead of at that caller side) *)
  | SW_inner_arg_temps

    (* allow (with %p) formatted printing of non-void pointers (relaxing ISO) *)
  | SW_permissive_printf

    (* make it so every object allocation is zero initialised *)
  | SW_zero_initialised

  (* pointer revocation *)
  | SW_revocation of [ `INSTANT | `CORNUCOPIA]

  (* parsing of magic comments (e.g. "/*@ magic() @*/" as statements *)
  | SW_at_magic_comments

val get_switches: unit -> cerb_switch list
val has_switch: cerb_switch -> bool
val has_switch_pred: (cerb_switch -> bool) -> cerb_switch option
val set: string list -> unit

val set_iso_switches: unit -> unit

val is_CHERI: unit -> bool
val is_PNVI: unit -> bool
val has_strict_pointer_arith: unit -> bool
