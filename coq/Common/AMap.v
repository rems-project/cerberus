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

End AddressValue_as_ExtOT.

Module AMap <: FMapExt AddressValue_as_ExtOT.
  Include FMapExt.FMapExt(AddressValue_as_ExtOT).
End AMap.
