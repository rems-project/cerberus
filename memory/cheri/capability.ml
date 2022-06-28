module Z = struct
  include Nat_big_num
  let format = Z.format
  let equal_num = equal
end

module type Cap_permission = sig
  type t [@@deriving eq,show]

  (** the number of user-defined flags *)
  val user_perms_len: int

  (* it is a permssion in RISV but in Morello spec while it is
     encoded and treated as one, it is sigled out as separate
     field of logical Capability structure (see R_HRVBQ paragraph
     in Morello spec. *)
  val perm_is_global: t -> bool
  val perm_is_execute: t -> bool
  val perm_is_ccall: t -> bool
  val perm_is_load: t -> bool
  val perm_is_load_cap: t -> bool
  val perm_is_seal: t -> bool
  val perm_is_store: t -> bool
  val perm_is_store_cap: t -> bool
  val perm_is_store_local_cap: t -> bool
  val perm_is_system_access: t -> bool
  val perm_is_unseal: t -> bool

  (** User-defined permissions *)
  val get_user_perms: t -> bool list (* TODO: enforce user_perms_len? *)

  (* Clearing permissions *)
  val perm_clear_global: t -> t
  val perm_clear_execute: t -> t
  val perm_clear_ccall: t -> t
  val perm_clear_load: t -> t
  val perm_clear_load_cap: t -> t
  val perm_clear_seal: t -> t
  val perm_clear_store: t -> t
  val perm_clear_store_cap: t -> t
  val perm_clear_store_local_cap: t -> t
  val perm_clear_system_access: t -> t
  val perm_clear_unseal: t -> t

  (** perform bitwise AND of user permissions *)
  val perm_and_user_perms: t -> bool list -> t

  (** null permission *)
  val perm_p0: t

  (** permissions for newly allocated region *)
  val perm_alloc: t

  (** permissions for newly allocated functin *)
  val perm_alloc_fun: t

  (* --- Utility methods --- *)

  val to_string: t -> string
  (* raw permissoins in numeric format *)
  val to_raw: t -> Z.num

  (* Initialize from list of boolean. The size and
     contents of the list is implementation-specific.
     Returns None in case of error *)
  val of_list: bool list -> t option

  (* inverse of [of_list] *)
  val to_list: t -> bool list

end

module type Capability =
  sig
    module P: Cap_permission

    type t [@@deriving eq,show]

    (** This is a new integer type introduced by CHERI C and should be
        used to hold virtual addresses. vaddr_t should not be directly
        cast to a pointer type for dereference; instead, it must be
        combined with an existing valid capability to the address
        space to generate a dereferenceable pointer. *)
    type vaddr
    type otype

    type vaddr_interval
    type cap_seal_t

    (* Properties of [vadr] *)

    val min_vaddr : vaddr
    val max_vaddr : vaddr
    val sizeof_vaddr: int

    val vaddr_bitwise_complement: vaddr -> vaddr

    (** the number of user-defined flags *)
    val cap_flags_len: int

    val cap_is_valid : t -> bool

    val cap_get_value : t -> vaddr

    val cap_get_offset : t -> Z.num

    val cap_get_obj_type : t -> otype

    (** Returns bounds in form [base,limit) for covered  memory region. base is inclusive while limit is exclusive *)
    val cap_get_bounds: t -> vaddr_interval

    (** Get informaiton about "seal" on this capability *)
    val cap_get_seal: t -> cap_seal_t

    (** user-defined flags *)
    val cap_get_flags: t -> bool list (* TODO: enforce cap_flags_len? *)

    val cap_get_perms: t -> P.t

    (** Null capability *)
    val cap_c0: unit -> t

    (** Capability for newly allocated region *)
    val alloc_cap: vaddr -> vaddr -> t

    (** Capability to allocate function *)
    val alloc_fun: vaddr -> t

    (** Due to encoding, not all capabilities with large bounds have a
        contiguous representable region. This representability check is
        applied when manipulating a Capability Value

        For example, in Morello: if modifying a Capability Value causes
        the bounds to change, a representabilty check fails. Some
        versions of the check may fail in additional cases.

        See: `CapIsRepresentable` in Morello *)
    val cap_vaddr_representable: t -> vaddr -> bool

    (** Whenever given bounds could be encoded exactly. Due to
        encoding issues not all bounds could be reprsented exactly
        (e.g. due to alignment).

        See: `CapIsRepresentable` in Morello *)
    val cap_bounds_representable_exactly: t -> vaddr_interval -> bool

    (* Operations on capabilities.

       See also:
       - Section "2.6 Manipulating Capabilities" in Morello spec.
     *)

    (** AKA "clear tag" *)
    val cap_invalidate : t -> t

    (* --- Monotonic manipulation -- *)

    (** Modifying the Capability Value (vaddress of object type)

        Related instructions:
        - CFromPtr in RISC V
        - CSetVaddr in RISC V
        - SCVALUE in Morello
        - CCopyType in RISC V
        - CPYTYPE in Morello
     *)
    val cap_set_value: t -> vaddr -> t

    (** Reducing the Capability Bounds (with rounding)

        Related instructions:
        - CSetBounds in RISCV
        - SCBNDS (immediate) in Morello?
     *)
    val cap_narrow_bounds: t -> vaddr_interval -> t

    (** Reducing the Capability Bounds (exact)

        Related instructions:
        - CSetBoundsExact in RISCV
        - SCBNDSE (immediate) in Morello?
     *)
    val cap_narrow_bounds_exact: t -> vaddr_interval -> t

    (** Reducing the Capability Permissions

        Related instructions:
        - CAndPerm in RISC V
        - CLRPERM in Morello
     *)
    val cap_narrow_perms: t -> P.t -> t

    (* Sealing operations *)

    (** Regular sealing (with object type)

        Related instructions:
        - CSeal in RISC V.
        - SEAL (capabilitiy) in Morello
     *)
    val cap_seal: t -> t -> t

    (** Seal Entry
        - CSealEntry in RISC V.
        - SEAL (immediatete) in Morello
     *)
    val cap_seal_entry: t -> t

    (** Seal Indirect Entry
        - CInvokeInd proposed but not implmented RISC V
        - SEAL (immediatete) in Morello
     *)
    val cap_seal_indirect_entry: t -> t

    (** Seal Entry Pair
        - proposed but not implmented in in RISC V.
        - SEAL (immediatete) in Morello
     *)
    val cap_seal_indirect_entry_pair: t -> t

    (** Modifying the Capability Flags
        - BICFLGS in Morello
        - EORFLGS in Morello
        - ORRFLGS in Morello
        - SCFLGS in Morello
     *)
    val cap_set_flags: t -> bool list -> t

    (* --- Controlled non-monotonic manipulation --  *)

    (** Unsealing a capability using an unsealing operation.
        - CUnseal in RISCV
        - UNSEAL in Morello
     *)
    val cap_unseal: t -> t -> t

    (* --- Encoding/decoding to list of bytes --- *)

    (** Decoding sequence of bytes into capbility object. It will
        return None if list is wrong size. Validity tag is passed
        separately, as it is not part of encoding.  *)
    val decode: char list -> bool -> t option

    (** Encode capability as list of bytes.

        boolean agrument specify if bounds needs to be encoded
        exactly.  if exact encoding requested but no possible, invalid
        capability will be returned.

        Retuns memory-encoded capability and validy tag
     *)
    val encode: bool ->  t -> (char list * bool)

    (* --- Compression-related --- *)

    (** returns the length that a capability would have after using
        [cheri_bounds_set] to set the length to [len] (assuming
        appropriate alignment of the base). *)
    val representable_length: Z.num -> Z.num

    (** returns a bitmask that can be used to align an address downwards
        such that it is sufficiently aligned to create a precisely
        bounded capability. *)
    val representable_alignment_mask: Z.num -> Z.num


    (* --- Utility methods --- *)

    val to_string: t -> string
    val strfcap: string -> t -> string option

    val cap_is_null_derived: t -> bool

    (* --- Equality --- *)

    (** exact equality. compares capability metadata as well as value *)
    val eq: t -> t -> bool

    (** compare value only ignoring metadata. [value_compare x y]
        returns [0] if [cap_get_value x] is equal to [cap_get_value
        y], a negative integer if [cap_get_value x] is less than
        [cap_get_value y], and a positive integer if [cap_get_value x]
        is greater than [cap_get_value y].  *)
    val value_compare: t -> t -> int

    (**
       Exact comparison including metadata
       - CMP/SUBS in Morello
     *)
    val exact_compare: t -> t -> int

  end
