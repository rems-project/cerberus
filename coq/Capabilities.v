(* Coq formalization on CHERI Capablities *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

Require Import Addr.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Open Scope Z_scope.
Open Scope list_scope.

Module Type Permission.
  Parameter t:Set.
  Parameter user_perms_len: nat.

  (* Convenience functions to examine some permission bits *)

  (* it is a permssion in RISV but in Morello spec while it is encoded
     and treated as one, it is sigled out as separate field of logical
     Capability structure (see R_HRVBQ paragraph in Morello spec. *)
  Parameter perm_is_global: t -> bool.

  Parameter perm_is_execute: t -> bool.
  Parameter perm_is_ccall: t -> bool.
  Parameter perm_is_load: t -> bool.
  Parameter perm_is_load_cap: t -> bool.
  Parameter perm_is_seal: t -> bool.
  Parameter perm_is_store: t -> bool.
  Parameter perm_is_store_cap: t -> bool.
  Parameter perm_is_store_local_cap: t -> bool.
  Parameter perm_is_system_access: t -> bool.
  Parameter perm_is_unseal: t -> bool.

  (* User-defined permissions *)
  Parameter get_user_perms: t -> list bool.

  (* Clearing permissions *)
  Parameter perm_clear_global: t -> t.
  Parameter perm_clear_execute: t -> t.
  Parameter perm_clear_ccall: t -> t.
  Parameter perm_clear_load: t -> t.
  Parameter perm_clear_load_cap: t -> t.
  Parameter perm_clear_seal: t -> t.
  Parameter perm_clear_store: t -> t.
  Parameter perm_clear_store_cap: t -> t.
  Parameter perm_clear_store_local_cap: t -> t.
  Parameter perm_clear_system_access: t -> t.
  Parameter perm_clear_unseal: t -> t.


  (** perform bitwise AND of user permissions *)
  Parameter perm_and_user_perms: t -> list bool -> t.

  (** null permission *)
  Parameter perm_p0: t.

  (** permissions for newly allocated region *)
  Parameter perm_alloc: t.

  (** permissions for newly allocated function *)
  Parameter perm_alloc_fun: t.

  (* --- Utility methods --- *)

  Parameter to_string: t -> string.

  (* raw permissoins in numeric format *)
  Parameter to_raw: t -> Z.

  (* Initialize from list of boolean. The size and
     contents of the list is implementation-specific.
     Returns None in case of error *)
  Parameter of_list: list bool -> option t.

  (* inverse of [of_list] *)
  Parameter to_list: t -> list bool.
End Permission.

Module Type OTYPE.
  Parameter t:Set.
End OTYPE.

Module Type CAP_SEAL_T.
  Parameter t:Set.
End CAP_SEAL_T.

Module Type VADDR_INTERVAL (V:VADDR).
  Parameter Inline t: Set.

  Parameter addresses_in_interval: t -> V.t -> bool.
  Parameter ltb: t -> t -> bool.
End VADDR_INTERVAL.

Module Type Capability
  (V:VADDR)
  (OT:OTYPE)
  (S:CAP_SEAL_T)
  (I:VADDR_INTERVAL V)
  (P:Permission).

  Parameter t: Set.

  (* Properties of [vadr] *)

  Parameter min_vaddr : V.t.
  Parameter max_vaddr : V.t.
  Parameter sizeof_vaddr: nat.

  (** the number of user-defined flags *)
  Parameter cap_flags_len: nat.

  Parameter cap_is_valid : t -> bool.

  Parameter cap_get_value : t -> V.t.

  Parameter cap_get_offset : t -> Z.

  Parameter cap_get_obj_type : t -> OT.t.

  (** Returns bounds in form [base,limit) for covered  memory region. base is inclusive while limit is exclusive *)
  Parameter cap_get_bounds: t -> I.t.

  (** Get informaiton about "seal" on this capability *)
  Parameter cap_get_seal: t -> S.t.

  (** user-defined flags *)
  Parameter cap_get_flags: t -> list bool. (* TODO: enforce cap_flags_len? *)

  Parameter cap_get_perms: t -> P.t.

  (** Null capability *)
  Parameter cap_c0: unit -> t.

  (** Capability for newly allocated region *)
  Parameter alloc_cap: V.t -> V.t -> t.

  (** Capability to allocate function *)
  Parameter alloc_fun: V.t -> t.

  (** Due to encoding, not all capabilities with large bounds have a
        contiguous representable region. This representability check is
        applied when manipulating a Capability value

        For example, in Morello: if modifying a Capability value causes
        the bounds to change, a representabilty check fails. Some
        versions of the check may fail in additional cases.

        See: `CapIsRepresentable` in Morello *)
  Parameter cap_vaddr_representable: t -> V.t -> bool.

  (** Whenever given bounds could be encoded exactly. Due to
        encoding issues not all bounds could be reprsented exactly
        (e.g. due to alignment).

        See: `CapIsRepresentable` in Morello *)
  Parameter cap_bounds_representable_exactly: t -> I.t -> bool.

  (* Operations on capabilities.

       See also:
       - Section "2.6 Manipulating Capabilities" in Morello spec.
   *)

  (** AKA "clear tag" *)
  Parameter cap_invalidate : t -> t.

  (* --- Monotonic manipulation -- *)

  (** Modifying the Capability value (V.tess of object type)

        Related instructions:
        - CFromPtr in RISC V
        - CSetV.T in RISC V
        - SCPARAMETERUE in Morello
        - CCopyType in RISC V
        - CPYTYPE in Morello
   *)
  Parameter cap_set_value: t -> V.t -> t.

  (** Reducing the Capability Bounds (with rounding)

        Related instructions:
        - CSetBounds in RISCV
        - SCBNDS (immediate) in Morello?
   *)
  Parameter cap_narrow_bounds: t -> I.t -> t.

  (** Reducing the Capability Bounds (exact)

        Related instructions:
        - CSetBoundsExact in RISCV
        - SCBNDSE (immediate) in Morello?
   *)
  Parameter cap_narrow_bounds_exact: t -> I.t -> t.

  (** Reducing the Capability Permissions

        Related instructions:
        - CAndPerm in RISC V
        - CLRPERM in Morello
   *)
  Parameter cap_narrow_perms: t -> P.t -> t.

  (* Sealing operations *)

  (** Regular sealing (with object type)

        Related instructions:
        - CSeal in RISC V.
        - SEAL (capabilitiy) in Morello
   *)
  Parameter cap_seal: t -> t -> t.

  (** Seal Entry
        - CSealEntry in RISC V.
        - SEAL (immediatete) in Morello
   *)
  Parameter cap_seal_entry: t -> t.

  (** Seal Indirect Entry
        - CInvokeInd proposed but not implmented RISC V
        - SEAL (immediatete) in Morello
   *)
  Parameter cap_seal_indirect_entry: t -> t.

  (** Seal Entry Pair
        - proposed but not implmented in in RISC V.
        - SEAL (immediatete) in Morello
   *)
  Parameter cap_seal_indirect_entry_pair: t -> t.

  (** Modifying the Capability Flags
        - BICFLGS in Morello
        - EORFLGS in Morello
        - ORRFLGS in Morello
        - SCFLGS in Morello
   *)
  Parameter cap_set_flags: t -> list bool -> t.

  (* --- Controlled non-monotonic manipulation --  *)

  (** Unsealing a capability using an unsealing operation.
        - CUnseal in RISCV
        - UNSEAL in Morello
   *)
  Parameter cap_unseal: t -> t -> t.

  (* --- Encoding/decoding to list of bytes --- *)

  (** Decoding sequence of bits into a capbility object. It will
        return None if list is wrong size. validity tag is passed
        separately, as it is not part of encoding.  *)
  Parameter decode: Z -> bool -> option t.

  (** Encode capability as list of bits.

        boolean agrument specify if bounds needs to be encoded
        exactly.  if exact encoding requested but no possible, inParameterid
        capability will be returned.

        Retuns memory-encoded capability and validity tag
   *)
  Parameter encode: bool ->  t -> (Z * bool).

  (* --- Compression-related --- *)

  (** returns the length that a capability would have after using
        [cheri_bounds_set] to set the length to [len] (assuming
        appropriate alignment of the base).
   *)
  Parameter representable_length: Z -> Z.

  (** returns a bitmask that can be used to align an address downwards
        such that it is sufficiently aligned to create a precisely
        bounded capability.
   *)
  Parameter representable_alignment_mask:  Z -> Z.

  (* --- Utility methods --- *)

  Parameter to_string: t -> string.
  Parameter strfcap: string -> t -> option string.

  Parameter cap_is_null_derived: t -> bool.

  (* --- Equality --- *)

  (** exact equality. compares capability metadata as well as value *)
  Parameter eqb: t -> t -> bool.

  (** compare value only ignoring metadata. *)
  Parameter value_compare: t -> t -> comparison.

  (**
       Exact comparison including metadata
       - CMP/SUBS in Morello
   *)
  Parameter exact_compare: t -> t -> comparison.

  (* Make sure `eqb` and `eqb_exact_compare` are consistent *)
  Parameter eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.

  (* Make sure `eqb` and `value_compare` are consistent *)
  Parameter eqb_value_compare: forall a b, eqb a b = true -> value_compare a b = Eq.

End Capability.
