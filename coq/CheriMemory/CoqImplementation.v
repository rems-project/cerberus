
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Require Import CoqIntegerType.
Require Import CoqCtype.

Require Import AltBinNotations.

Require Import StructTact.StructTactics.

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
    typeof_enum: CoqSymbol.sym -> integerType;
  }.

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
  Parameter ichar_size:  (sizeof_ity get (CoqIntegerType.Signed CoqIntegerType.Ichar) = Some 1).
  Parameter uchar_size:  (sizeof_ity get (CoqIntegerType.Unsigned CoqIntegerType.Ichar) = Some 1).
End Implementation.

Module MorelloImpl : Implementation.

  Definition is_signed_ity_impl ity :=
    match ity with
    | Char => true
    | Bool => false
    | Signed _ => true
    | Unsigned _ => false
    | Enum tag_sym => true (* TODO: we do not handle registered enums *)
    | Size_t =>  false
    | Wchar_t => true
    | Wint_t =>  true
    | Ptrdiff_t => true
    | Ptraddr_t => false
    end.

  Definition sizeof_ity_impl x
    :=  match x with
        | Char
        | Bool => Some 1
        | Signed ibty
        | Unsigned ibty =>
          Some (match ibty with
            | Ichar => 1
            | Short => 2
            | Int_ => 4
            | Long
            | LongLong => 8
            | IntN_t n
            | Int_leastN_t n
            | Int_fastN_t n => max 1 (Nat.div n 8)
            | Intmax_t
            | Intptr_t => 16
            end)
        | Enum ident => Some 4 (* TODO: we do not handle registered enums *)
        | Wchar_t
        | Wint_t => Some 4
        | Size_t
        | Ptrdiff_t => Some 8
        | Ptraddr_t => Some 8
        end.

  Definition precision_ity_impl ity : option Z :=
    match sizeof_ity_impl ity with
    | Some n =>
        let zn := Z.of_nat n in
        if is_signed_ity_impl ity then
          Some (8*zn-1)%Z
        else
          Some (8*zn)%Z
    | None =>
        None
    end.

  Definition sizeof_fty_impl x
    := match x with
       | RealFloating Float =>
           Some 8 (* TODO:hack ==> 4 *)
       | RealFloating Double =>
           Some 8
       | RealFloating LongDouble =>
           Some 8 (* TODO:hack ==> 16 *)
       end.

  Definition alignof_fty_impl x : nat
    := match x with
       | RealFloating Float =>
           8 (* TODO:hack ==> 4 *)
       | RealFloating Double =>
           8
       | RealFloating LongDouble =>
           8 (* TODO:hack ==> 16 *)
       end.

  Definition alignof_ity_impl x : nat :=
    match x with
    | Char
    | Bool => 1
    | Signed ibty
    | Unsigned ibty =>
        (match ibty with
         | Ichar => 1
         | Short => 2
         | Int_ => 4
         | Long
         | LongLong => 8
         | IntN_t n
         | Int_leastN_t n
         | Int_fastN_t n => max 1 (Nat.div n 8)
         | Intmax_t
         | Intptr_t => 16
         end)
    | Enum ident => 4 (* TODO: we do not handle registered enums *)
    | Wchar_t
    | Wint_t => 4
    | Size_t
    | Ptrdiff_t => 8
    | Ptraddr_t => 8
    end.

  (* fixing enum type for simplicity. *)
  Definition typeof_enum_impl (_:CoqSymbol.sym)
             := Signed Int_.

  Program Definition get :=
    {|
      name            := "clang11_aarch64-unknown-freebsd13";
      details         := "clang version 11.0.0\nTarget: Morello";
      sizeof_pointer  := 16;
      alignof_pointer := 16 ;
      is_signed_ity   := is_signed_ity_impl;
      sizeof_ity      := sizeof_ity_impl;
      precision_ity   := precision_ity_impl;
      sizeof_fty      := sizeof_fty_impl;
      alignof_ity     := alignof_ity_impl;
      alignof_fty     := alignof_fty_impl;
      typeof_enum     := typeof_enum_impl;
    |}.

  Lemma ichar_size:  (sizeof_ity get (CoqIntegerType.Signed CoqIntegerType.Ichar) = Some 1).
  Proof. reflexivity. Qed.

  Lemma uchar_size:  (sizeof_ity get (CoqIntegerType.Unsigned CoqIntegerType.Ichar) = Some 1).
  Proof. reflexivity. Qed.

  Lemma alignof_pointer_pos: 0 < (alignof_pointer get).
  Proof. cbn; lia. Qed.

  Lemma alignof_ity_pos: forall ty, 0< (alignof_ity get ty).
  Proof.
    intros ty.
    destruct ty; cbn;try lia.
    1,2: destruct i; cbn;try lia.

    all: pose proof (Nat.divmod_spec n 7 0 7) as DM;
      assert(7<=7) as SV by lia;
      specialize (DM SV);
      remember (Nat.divmod n 7 0 7) as dm;
      destruct dm;
      cbn;
      destruct DM;
      destruct n0;lia.
  Qed.

  Lemma alignof_fty_pos: forall ty, 0< (alignof_fty get ty).
  Proof.
    intros ty.
    destruct ty; cbn;try lia.
    destruct r; lia.
  Qed.

  Lemma sizeof_ity_pos: forall ty x, sizeof_ity get ty = Some x -> 0 < x.
  Proof.
    intros ty x H.
    destruct ty;
      cbn in H; repeat break_match_hyp; inversion H; lia.
  Qed.

  Lemma sizeof_fty_pos: forall ty x, sizeof_fty get ty = Some x -> 0 < x.
  Proof.
    intros ty x H.
    destruct ty;
      cbn in H; repeat break_match_hyp; inversion H; lia.
  Qed.


End MorelloImpl.
