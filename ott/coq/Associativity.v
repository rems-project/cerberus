Require Import Common.
Require Import Implementation.
Require Import AilTypes.
Require Import AilTypesAux.

Require Import ZArith.
Open Local Scope Z.

Definition counter : implementation.
  make_implementation_tac
    Two'sComplement
    ( fun it =>
        match it with
        | Char | Signed   _ => true
        | Bool | Unsigned _ => false
        end
    )
    ( fun it =>
        match it with
        | Char => 7
        | Bool => 2
        | Signed   Ichar => 7
        | Unsigned Ichar => 8
        | Signed   Short => 15
        | Unsigned Short => 16
        | Signed   Int      => 127
        | Unsigned Int      => 128
        | Signed   Long     => 127
        | Unsigned Long     => 256
        | Signed   LongLong => 255
        | Unsigned LongLong => 256
        end
    )
    (Unsigned Long)
    (Signed   Long).
Defined.

Lemma non_assoc :
  exists P it1 it2 it3,
    usual_arithmetic_promoted_integer P it1 (usual_arithmetic_promoted_integer P it2 it3) 
     <>
    usual_arithmetic_promoted_integer P (usual_arithmetic_promoted_integer P it1 it2) it3.
Proof.
  exists counter, (Signed Long), (Unsigned Int), (Signed LongLong).
  discriminate.
Qed.
