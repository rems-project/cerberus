
type addr = Nat_big_num.num
type obj_type = Nat_big_num.num
type addr_interval = addr * addr

type cap_value =
  | CapAddress of addr
  | CapToken of obj_type

type cap_seal =
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  | Cap_Indirect_SEntry_Pair (* "LBP" in Morello *)
  | Cap_Sealed of obj_type

module type cap_permission = sig
  type t
  (* Number of user-defined flags *)
  val user_perms_len: int

  (* it is a permssion in RISV but in Morello spec while it is
     encoded and treated as one, it is sigled out as separate
     field of logical Capability structure (see R_HRVBQ paragraph
     in Morello spec. *)
  val permits_global: t -> bool
  val permits_execute: t -> bool
  val permits_ccall: t -> bool
  val permits_load: t -> bool
  val permits_load_cap: t -> bool
  val permits_seal: t -> bool
  val permits_store: t -> bool
  val permits_store_cap: t -> bool
  val permits_store_local_cap: t -> bool
  val permits_system_access: t -> bool
  val permits_unseal: t -> bool

  (* User-defined permissions *)
  val get_user_perms: t -> bool list (* TODO: enforce user_perms_len? *)

  (* TODO: how to change/clear permissions? *)
end

module type capability_func =
  functor (P: cap_permission) ->
  sig
    type t

    (* Number of user-defined flags *)
    val cap_flags_len: int

    val cap_is_valid : bool

    val cap_get_value : t -> cap_value

    (* Returns either inclusive bounds for covered  memory region *)
    val cap_get_bounds: t -> addr_interval

    (* Get informaiton about "seal" on this capability *)
    val cap_get_seal: t -> cap_seal

    (* user-defined flags *)
    val get_flags: t -> bool list (* TODO: enforce cap_flags_len? *)

    val get_perms: t -> P.t

    (* Null capability *)
    val cap_c0: t

    (* Boldly assuming this one never fails *)
    val cap_addr_of_obj_type: obj_type -> addr

    (* Due to encoding, not all capabilities with large bounds have a
       contiguous representable region. This representability check is
       applied when manipulating a Capability Value

       For example, in Morello: if modifying a Capability Value causes
       the bounds to change, a representabilty check fails. Some
       versions of the check may fail in additional cases.

       See: `CapIsRepresentable` in Morello *)
    val cap_addr_representable: t -> addr -> bool

    (* Whenever given bounds could be encoded exactly. Due to
       encoding issues not all bounds could be reprsented exactly
       (e.g. due to alignment).

       See: `CapIsRepresentable` in Morello *)
    val cap_bounds_representable_exactly: t -> addr_interval -> bool

    (* Operations on capabilities.

       See also:
       - Section "2.6 Manipulating Capabilities" in Morello spec.
     *)

    (* AKA "clear tag" *)
    val cap_invalidate : t -> t

    (* --- Monotonic manipulation -- *)

    (* Modifying the Capability Value (address of object type)

       Related instructions:
       - CFromPtr in RISC V
       - CSetAddr in RISC V
       - SCVALUE in Morello
       - CCopyType in RISC V
       - CPYTYPE in Morello
     *)
    val cap_set_value: t -> cap_value -> t

    (* Reducing the Capability Bounds (with rounding)

       Related instructions:
       - CSetBounds in RISCV
       - SCBNDS (immediate) in Morello?
     *)
    val cap_narrow_bounds: t -> addr_interval -> t

    (* Reducing the Capability Bounds (exact)

       Related instructions:
       - CSetBoundsExact in RISCV
       - SCBNDSE (immediate) in Morello?
     *)
    val cap_narrow_bounds_exact: t -> addr_interval -> t

    (* Reducing the Capability Permissions

       Related instructions:
       - CAndPerm in RISC V
       - CLRPERM in Morello
     *)
    val cap_narrow_perms: t -> P.t -> t

    (* Sealing operations *)

    (* Regular sealing (with object type)

       Related instructions:
       - CSeal in RISC V.
       - SEAL (capabilitiy) in Morello
     *)
    val cap_seal: t -> t -> t

    (* Seal Entry
       - CSealEntry in RISC V.
       - SEAL (immediatete) in Morello
     *)
    val cap_seal_entry: t -> t

    (* Seal Indirect Entry
       - CInvokeInd proposed but not implmented RISC V
       - SEAL (immediatete) in Morello
     *)
    val cap_seal_indirect_entry: t -> t

    (* Seal Entry Pair
       - proposed but not implmented in in RISC V.
       - SEAL (immediatete) in Morello
     *)
    val cap_seal_indirect_entry_pair: t -> t

    (* Modifying the Capability Flags
       - BICFLGS in Morello
       - EORFLGS in Morello
       - ORRFLGS in Morello
       - SCFLGS in Morello
     *)
    val cap_set_flags: t -> bool list -> t

    (* --- Controlled non-monotonic manipulation --  *)

    (* Unsealing a capability using an unsealing operation.
       - CUnseal in RISCV
       - UNSEAL in Morello
     *)
    val cap_unseal: t -> t -> t

  end
