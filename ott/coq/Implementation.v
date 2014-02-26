Require Import ZArith.

Require Import Range.
Require Import AilTypes.

Local Open Scope Z.

Inductive binaryMode :=
  | Two'sComplement   : binaryMode
  | One'sComplement   : binaryMode
  | SignPlusMagnitude : binaryMode.

(* From 6.3.1.1
— The rank of a signed integer type shall be greater than the rank of any signed integer
type with less precision.
— The rank of long long int shall be greater than the rank of long int, which
shall be greater than the rank of int, which shall be greater than the rank of short
int, which shall be greater than the rank of signed char.

Suppose precision P (long long int) < precision P (long int). Then ltRank P
(long long int) (long int). But the second bullet tells us that ltRank P (long
int) (long long int). So P (long int) ≤ precision P (long long int).
*)

Definition min_precision ibt : Z :=
  match ibt with
  | Ichar    => 8
  | Short    => 16
  | Int      => 16
  | Long     => 32
  | LongLong => 64
  end.

Record implementation := make_implementation {
  binary_mode : binaryMode;
  signed : integerType -> bool;
  precision : integerType -> Z;
  size_t : integerType;
  ptrdiff_t : integerType;

  signed_Signed   ibt : signed (Signed   ibt) = true;
  signed_Bool         : signed Bool           = false;
  signed_Unsigned ibt : signed (Unsigned ibt) = false;

  signed_size_t    : signed size_t    = false;
  signed_ptrdiff_t : signed ptrdiff_t = true;

  precision_ptrdiff_t : 16 <= precision ptrdiff_t;
  precision_size_t    : 16 <= precision size_t;

  precision_Char :  precision Char = if signed Char
                                       then precision (Signed   Ichar)
                                       else precision (Unsigned Ichar);

  precision_Bool            :  1 <= precision Bool;
  precision_Signed   ibt    :  min_precision ibt <= precision (Signed   ibt) + 1;
  precision_Unsigned ibt    :  min_precision ibt <= precision (Unsigned ibt);

  (* Follows from 6.2.6.2 #2:
       if there are M value bits in the signed type and N in the unsigned
       type, then M ≤ N
   *)
  le_precision_Signed_Unsigned ibt    : precision (Signed   ibt) <= precision (Unsigned    ibt);
  (* unsigned char has no padding. *)
  le_precision_Signed_Unsigned_Ichar  : precision (Signed Ichar) <  precision (Unsigned  Ichar);

  le_precision_Signed_Long_LongLong   : precision (Signed  Long) <= precision (Signed LongLong);
  le_precision_Signed_Int_Long        : precision (Signed   Int) <= precision (Signed     Long);
  le_precision_Signed_Short_Int       : precision (Signed Short) <= precision (Signed      Int);
  le_precision_Signed_Ichar_Short     : precision (Signed Ichar) <= precision (Signed    Short);

  (* follows from 6.2.5 #8 *)
  le_precision_Unsigned_Long_LongLong : precision (Unsigned  Long) <= precision (Unsigned LongLong);
  le_precision_Unsigned_Int_Long      : precision (Unsigned   Int) <= precision (Unsigned     Long);
  le_precision_Unsigned_Short_Int     : precision (Unsigned Short) <= precision (Unsigned      Int);
  le_precision_Unsigned_Ichar_Short   : precision (Unsigned Ichar) <= precision (Unsigned    Short);
  le_precision_Unsigned_Bool_Ichar    : precision Bool             <= precision (Unsigned    Ichar)
}.

Lemma precision_ge_one P it : 1 <= precision P it.
Proof.
  destruct it.
  + set (precision_Char P) as Hchar;
    case_eq (signed P Char); intros Heq; rewrite Heq in Hchar; clear Heq;
    set (precision_Signed P Ichar) as Hmin; simpl in Hmin;
    [|set (le_precision_Signed_Unsigned P Ichar)];
    omega.
  + exact (precision_Bool P).
  + set (precision_Signed P ibt) as Hmin.
    destruct ibt; simpl in Hmin; omega.
  + set (precision_Signed P ibt) as Hmin.
    set (le_precision_Signed_Unsigned P ibt).
    destruct ibt; simpl in Hmin; omega.
Defined.

Lemma two_p_ge_one : forall {p}, 0 <= p -> 1 <= 2^p.
Proof.
  apply (natlike_rec2).
  + simpl; omega.
  + intros z Hge_zero IH.
    rewrite (Z.pow_succ_r _ _ Hge_zero).
    omega.
Qed.

Definition integer_range_positive {p} : 1 <= p -> 0 <= 2^p - 1.
Proof.
  intros.
  assert (0 <= p) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integer_range_signed_lower1 {p} : 1 <= p -> -2^p <= 0.
Proof.
  intros.
  assert (0 <= p) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integer_range_signed_lower2 {p} : 1 <= p -> -2^p + 1 <= 0.
Proof.
  intros.
  assert (0 <= p) as Hge_zero by omega.
  set (two_p_ge_one Hge_zero).
  omega.
Qed.

Definition integer_range_signed1 {p} : 1 <= p -> -2^p <= 2^p - 1.
Proof.
  intros Hge_one.
  set (integer_range_positive  Hge_one).
  set (integer_range_signed_lower1 Hge_one).
  apply (Z.le_trans _ 0 _); assumption.
Qed.

Definition integer_range_signed2 {p} : 1 <= p -> -2^p + 1 <= 2^p - 1.
Proof.
  intros Hge_one.
  set (integer_range_positive  Hge_one).
  set (integer_range_signed_lower2 Hge_one).
  apply (Z.le_trans _ 0 _); assumption.
Qed.

Definition integer_range P it :=
  let prec := precision P it in
  if signed P it then
    match binary_mode P with
    | Two'sComplement   => @make_range (-2^prec)     (2^prec - 1) (integer_range_signed1 (precision_ge_one P _))
    | One'sComplement   => @make_range (-2^prec + 1) (2^prec - 1) (integer_range_signed2 (precision_ge_one P _))
    | SignPlusMagnitude => @make_range (-2^prec + 1) (2^prec - 1) (integer_range_signed2 (precision_ge_one P _))
    end
  else
    @make_range 0 (2^prec - 1) (integer_range_positive (precision_ge_one P _)).

Lemma le_one_min_precision ibt : 1 <= min_precision ibt.
Proof. destruct ibt; simpl; omega. Qed.

Lemma le_one_min_precision_sub_one ibt : 1 <= min_precision ibt - 1.
Proof. destruct ibt; simpl; omega. Qed.

Definition min_range_unsigned ibt :=
  let prec := min_precision ibt in
  @make_range 0 (2^prec - 1) (integer_range_positive (le_one_min_precision ibt)).

Definition min_range_signed ibt :=
  let prec := min_precision ibt - 1 in
  @make_range (-2^prec + 1) (2^prec - 1) (integer_range_signed2 (le_one_min_precision_sub_one ibt)). 

Definition min_integer_range it :=
  match it with
  | Char         => make_range (integer_range_positive (le_one_min_precision_sub_one Ichar))
  | Bool         => make_range Z.le_0_1
  | Unsigned ibt => min_range_unsigned ibt
  | Signed   ibt => min_range_signed   ibt
  end.

Ltac make_implementation_tac binMode signed precision size_t ptrdiff_t :=
  refine (make_implementation
    binMode
    signed
    precision
    size_t
    ptrdiff_t
    (fun _ => eq_refl)
    eq_refl
    (fun _ => eq_refl)
    eq_refl
    eq_refl
    _
    _
    eq_refl
    _
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    _ _ _ _ _ _ _ _ _ _);
  simpl; omega.

Definition min_implementation_signed_char : implementation.
  make_implementation_tac
    SignPlusMagnitude
    ( fun it =>
        match it with
        | Char | Signed   _ => true
        | Bool | Unsigned _ => false
        end
    )
    ( fun it =>
        match it with
        | Char => 7
        | Bool => 1
        | Signed   Ichar => 7
        | Unsigned Ichar => 8
        | Signed   Short => 15
        | Unsigned Short => 16
        | Signed   Int      => 15
        | Unsigned Int      => 16
        | Signed   Long     => 31
        | Unsigned Long     => 32
        | Signed   LongLong => 63
        | Unsigned LongLong => 64
        end
    )
    (Unsigned Long)
    (Signed   Long).
Defined.

Definition min_implementation_unsigned_char : implementation.
  make_implementation_tac
    SignPlusMagnitude
    ( fun it =>
        match it with
        | Signed   _ => true
        | Char | Bool | Unsigned _ => false
        end
    )
    ( fun it =>
        match it with
        | Char => 8
        | Bool => 1
        | Signed   Ichar => 7
        | Unsigned Ichar => 8
        | Signed   Short => 15
        | Unsigned Short => 16
        | Signed   Int      => 15
        | Unsigned Int      => 16
        | Signed   Long     => 31
        | Unsigned Long     => 32
        | Signed   LongLong => 63
        | Unsigned LongLong => 64
        end
    )
    (Unsigned Long)
    (Signed   Long).
Defined.
