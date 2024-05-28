(** Map indexed by [Z] *)

Require Import Coq.ZArith.BinInt.
Require Import Coq.Structures.OrderedTypeEx.

Require Import FMapExt.

Module Z_as_ExtOT : OrderedTypeExt with Definition t:=Z.
  Include Z_as_OT.

  Definition with_offset := Z.add.
  Definition of_nat := Z.of_nat.
  Definition of_Z (x:Z) := x.
  Definition to_Z (x:t) := x.

  Lemma OT_of_Z_to_Z:
    forall (x:t), of_Z  (to_Z x) = x.
  Proof.
    auto.
  Qed.

  Lemma with_offset_0:
    forall (a:t), with_offset a 0 = a.
  Proof.
    intros.
    unfold with_offset.
    apply Z.add_0_r.
  Qed.

End Z_as_ExtOT.

Module ZMap <: FMapExt Z_as_ExtOT.
  Include FMapExt.FMapExt(Z_as_ExtOT).
End ZMap.
