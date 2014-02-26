Require Import ZArith.

Require Import Common.
Require Import Implementation.
Require Import AilTypes.
Require Import AilTypesAux.

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

Eval compute in usual_arithmetic_promoted_integer counter (Signed Long) (usual_arithmetic_promoted_integer counter (Unsigned Int) (Signed LongLong)).
Eval compute in usual_arithmetic_promoted_integer counter (usual_arithmetic_promoted_integer counter (Signed Long) (Unsigned Int)) (Signed LongLong).
