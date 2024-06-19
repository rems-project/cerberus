(** Map indexed by [AddressValue.t] *)

Require Import Coq.ZArith.BinInt.
From Coq.Structures Require Import OrderedType OrderedTypeEx.
From CheriCaps.Morello Require Import Capabilities.

Require Import FMapExt.

Require Import Coq.FSets.FMapFacts.

Module AddressValue_as_ExtOT : OrderedTypeExt
  with Definition t:=AddressValue.t
  with Definition with_offset:=AddressValue.with_offset.

  Include AddressValue_as_OT.

  Definition with_offset := AddressValue.with_offset.
  Definition of_nat (x:nat) := AddressValue.of_Z (Z.of_nat x).
  Definition of_Z := AddressValue.of_Z.
  Definition to_Z := AddressValue.to_Z.

  Lemma OT_of_Z_to_Z:
    forall (x:t), of_Z  (to_Z x) = x.
  Proof.
    intros x.
    unfold AddressValue.of_Z, AddressValue.to_Z.
    unfold bv_to_Z_unsigned.
    apply bitvector.Z_to_bv_bv_unsigned.
  Qed.

  Lemma with_offset_0:
    forall (a:t), with_offset a 0 = a.
  Proof.
    intros a.
    unfold with_offset, AddressValue.with_offset.
    rewrite Z.add_0_r.
    apply OT_of_Z_to_Z.
  Qed.

End AddressValue_as_ExtOT.

Module AMap <: FMapExt AddressValue_as_ExtOT.
  Include FMapExt.FMapExt(AddressValue_as_ExtOT).
End AMap.
