(* Coq formalization on CHERI Capablities *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.

From CheriCaps.Common Require Import Addr Capabilities.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Open Scope Z_scope.
Open Scope list_scope.


Record CapGhostState :=
  {
    tag_unspecified : bool;
    bounds_unspecified : bool
  }.

Definition ghost_state_eqb (a b:CapGhostState) : bool :=
  andb
    (eqb a.(tag_unspecified) b.(tag_unspecified))
    (eqb a.(bounds_unspecified) b.(bounds_unspecified)).

Definition Default_CapGhostState : CapGhostState
  := {| tag_unspecified := false; bounds_unspecified := false |}.

Module Type CAPABILITY_GS
  (V:PTRADDR)
  (F:FLAGS)
  (OT:OTYPE)
  (S:CAP_SEAL_T)
  (I:PTRADDR_INTERVAL V)
  (P:PERMISSIONS) <: CAPABILITY (V) (F) (OT) (S) (I) (P).

  Parameter t: Set.

  (* Properties of [vadr] *)

  Parameter min_ptraddr : V.t.
  Parameter max_ptraddr : V.t.
  Parameter sizeof_ptraddr: nat.
  Parameter sizeof_cap: nat.

  (** the number of user-defined flags *)
  
  (** ghost state management **)

  Parameter get_ghost_state: t -> CapGhostState.

  Parameter set_ghost_state: t -> CapGhostState -> t.

  (** access to various cap fields **)

  Parameter cap_is_valid : t -> bool.

  Parameter cap_get_value : t -> V.t.

  Parameter cap_get_offset : t -> Z.

  Parameter cap_get_obj_type : t -> OT.t.

  (** Returns bounds in form [base,limit) for covered  memory region. base is inclusive while limit is exclusive *)
  Parameter cap_get_bounds: t -> I.t.

  (** Get information about "seal" on this capability *)
  Parameter cap_get_seal: t -> S.t.

  (** user-defined flags *)
  Parameter cap_get_flags: t -> F.t.
  
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
  Parameter cap_ptraddr_representable: t -> V.t -> bool.

  (** Whenever given bounds could be encoded exactly. Due to
        encoding issues not all bounds could be reprsented exactly
        (e.g. due to alignment).
        See: `CapIsRepresentable` in Morello *)
  Parameter cap_bounds_representable_exactly: t -> I.t -> bool.

  (* Check if all addresses in given interval are within the bounds of
     given capability *)
  Parameter cap_bounds_check: t -> I.t -> bool.

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

  (** Reducing the Capability Permissions. 
      The input permissions should be the ones to be kept.
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

  (* Returns true if the input capability is sealed
     See also CapIsSealed in Morello
   *)
  Parameter cap_is_sealed: t -> bool.

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
  Parameter cap_set_flags: t -> F.t -> t. 

  (* --- Controlled non-monotonic manipulation --  *)

  (** Unsealing a capability using an unsealing operation.
        - CUnseal in RISCV
        - UNSEAL in Morello
   *)
  Parameter cap_unseal: t -> t -> t.

  (* --- Encoding/decoding to list of bytes --- *)

  (** Decoding sequence of bytes into a capability object. It will
        return None if list is of the wrong size. validity tag is passed
        separately, as it is not part of encoding.  *) 
  Parameter decode: list ascii -> bool -> option t.

  (** Encode capability as list of bytes.
        Retuns memory-encoded capability and validity tag.
   *)
  Parameter encode: t -> option ((list ascii) * bool).

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
  Parameter representable_alignment_mask: Z -> Z.

  (* --- Utility methods --- *)

  Parameter to_string: t -> string.       
  
  Parameter strfcap: string -> t -> option string.

  Parameter cap_is_null_derived: t -> bool.

  (* --- Equality --- *)

  (** exact equality. compares capability metadata as well as value *) 
  Parameter eqb: t -> t -> bool.

  (** compare value only, ignoring metadata. *)
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

  Parameter cap_invalidate_invalidates: forall c, cap_is_valid (cap_invalidate c) = false.

  Parameter cap_invalidate_preserves_value: forall c, cap_get_value c = cap_get_value (cap_invalidate c).

  Parameter cap_get_set_value: forall (c:t) (a:V.t), cap_get_value (cap_set_value c a) = a.

  Parameter cap_encode_length:
    forall c l t, encode c = Some (l, t) -> List.length l = sizeof_cap.

  Parameter cap_encode_valid:
    forall cap cb b,
      cap_is_valid cap = true -> encode cap = Some (cb, b) -> b = true.

  Parameter cap_encode_decode_bounds:
    forall cap bytes t,
      encode cap = Some (bytes, t) ->
      exists cap', decode bytes t = Some cap'
              /\ cap_get_bounds cap = cap_get_bounds cap'.

End CAPABILITY_GS.
