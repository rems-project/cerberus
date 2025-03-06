
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Require Import IntegerType.
Require Import Ctype.

Require Import AltBinNotations.


Record implementation := {
    name: string;
    details: string;
    sizeof_pointer: nat;
    alignof_pointer: nat;
    is_signed_ity: integerType -> bool;
    sizeof_ity: integerType -> option nat;
    precision_ity: integerType -> option Z;
    sizeof_fty: floatingType -> option nat;
    alignof_ity: integerType -> nat;
    alignof_fty: floatingType -> nat;
    typeof_enum: Symbol.sym -> integerType;
  }.

Local Open Scope nat_scope.

Module Type Implementation.

  Parameter get: implementation.

  (* -- Sanity properties for proofs -- *)

  (* basic types sizes positive *)
  Parameter alignof_pointer_pos: 0 < (alignof_pointer get).
  Parameter sizeof_ity_pos: forall ty x, sizeof_ity get ty = Some x -> 0 < x.
  Parameter sizeof_fty_pos: forall ty x, sizeof_fty get ty = Some x -> 0 < x.

  (* alignments start from 1 *)
  Parameter alignof_ity_pos: forall ty, 0 < (alignof_ity get ty).
  Parameter alignof_fty_pos: forall ty, 0 < (alignof_fty get ty).

  (* Per C17 (6.5.3.4): "When sizeof is applied to an operand that has type char, unsigned
     char, or signed char, (or a qualified version thereof) the result
     is 1." *)
  Parameter ichar_size:  (sizeof_ity get (IntegerType.Signed IntegerType.Ichar) = Some 1).
  Parameter uchar_size:  (sizeof_ity get (IntegerType.Unsigned IntegerType.Ichar) = Some 1).

End Implementation.

