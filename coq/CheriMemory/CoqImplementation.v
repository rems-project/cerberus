
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Require Import CoqIntegerType.
Require Import CoqCtype.

Local Open Scope Z_scope.
Require Import AltBinNotations.


Record implementation := {
    name: string;
    details: string;
    sizeof_pointer: Z;
    alignof_pointer: Z;
    is_signed_ity: integerType -> bool;
    sizeof_ity: integerType -> option Z;
    precision_ity: integerType -> option Z;
    sizeof_fty: floatingType -> option Z;
    alignof_ity: integerType -> Z;
    alignof_fty: floatingType -> Z;
    typeof_enum: CoqSymbol.sym -> integerType;
  }.

Module Type Implementation.
  Parameter get: implementation.

  (* Sanity properties for proofs *)
  Parameter ichar_size_exists:  (exists csz, sizeof_ity get (CoqIntegerType.Unsigned CoqIntegerType.Ichar) = Some csz).
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
            | Int_fastN_t n => Z.div (Z.of_nat n) 8
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

  Definition precision_ity_impl ity :=
    match sizeof_ity_impl ity with
    | Some n =>
        if is_signed_ity_impl ity then
          Some (8*n-1)
        else
          Some (8*n)
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

  Definition alignof_fty_impl x
    := match x with
       | RealFloating Float =>
           8 (* TODO:hack ==> 4 *)
       | RealFloating Double =>
           8
       | RealFloating LongDouble =>
           8 (* TODO:hack ==> 16 *)
       end.

  Definition alignof_ity_impl x :=
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
         | Int_fastN_t n => Z.div (Z.of_nat n) 8
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

  Lemma ichar_size_exists:
    (exists csz, sizeof_ity get (CoqIntegerType.Unsigned CoqIntegerType.Ichar) = Some csz).
  Proof.
    exists 1.
    reflexivity.
  Qed.


End MorelloImpl.
