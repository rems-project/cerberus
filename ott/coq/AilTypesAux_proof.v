Require Import Bool.
Require Import ZArith.
Require Import Omega.
Require Import Coq.Classes.RelationClasses.

Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux.
Require Import AilTypesAux_fun.
Require Import Implementation.

Local Open Scope Z.

Lemma isUnqualified_fun_correct qs :
  boolSpec (isUnqualified_fun qs) (isUnqualified qs).
Proof. do 2 unfold_goal. repeat context_destruct. Qed.

(*
Fixpoint typeEquiv_fun_correct t1 t2 :
  boolSpec (typeEquiv_fun t1 t2) (typeEquiv t1 t2)
with typeEquiv_params_fun_correct p1 p2 :
  boolSpec (typeEquiv_params_fun p1 p2) (typeEquiv_params p1 p2).
Proof.
- do 2 unfold_goal.
  destruct t1;
  destruct t2;
  fold typeEquiv_params_fun;
  fold typeEquiv_fun;
  unfold andb;
  repeat match goal with
  | [|- bool_of_decision ?e = ?o -> _] => is_var o; destruct e; subst; intros ?; subst o; simpl
  | [|- list_equiv_fun _ ?qs1 ?qs2 = ?o -> _] => is_var o; case_fun (list_equiv_fun_correct qs1 qs2 (fun x y => Decision_boolSpec (decide x y)))
  | [|- typeEquiv_fun ?t1 ?t2 = ?o -> _] => is_var o; case_fun (typeEquiv_fun_correct t1 t2)
  | [|- typeEquiv_params_fun ?p1 ?p2 = ?o -> _] => is_var o; case_fun (typeEquiv_params_fun_correct p1 p2)
  | [|- typeEquiv _ _] => constructor; assumption
  | [|- neg (typeEquiv _ _)] => now inversion 1
  |_ => context_destruct
  end.
-do 2 unfold_goal.
  destruct p1;
  destruct p2;
  fold typeEquiv_fun;
  fold typeEquiv_params_fun;
  unfold andb;
  repeat match goal with
  | [|- bool_of_decision ?e = ?o -> _] => is_var o; destruct e; subst; intros ?; subst o; simpl
  | [|- list_equiv_fun _ ?qs1 ?qs2 = ?o -> _] => is_var o; case_fun (list_equiv_fun_correct qs1 qs2 (fun x y => Decision_boolSpec (decide x y)))
  | [|- typeEquiv_fun ?t1 ?t2 = ?o -> _] => is_var o; case_fun (typeEquiv_fun_correct t1 t2)
  | [|- typeEquiv_params_fun ?p1 ?p2 = ?o -> _] => is_var o; case_fun (typeEquiv_params_fun_correct p1 p2)
  | [|- typeEquiv_params _ _] => constructor; assumption
  | [|- neg (typeEquiv_params _ _)] => now inversion 1
  |_ => context_destruct
  end.
Qed.
*)

(* Equations
Require Import Equations.
*)

(*Equations
isInteger_dec t : Decision (isInteger t) :=
isInteger_dec (Basic (Integer _)) := inl (IsInteger _);
isInteger_dec _                   := inr _.
*)

Lemma isInteger_fun_correct t : boolSpec (isInteger_fun t) (isInteger t).
Proof. destruct t; my_auto. Qed.

Instance isInteger_dec t : Decision (isInteger t) := boolSpec_Decision (isInteger_fun_correct t).

(* Equations
isVoid_dec t : Decision (isVoid t) :=
isVoid_dec Void := inl IsVoid;
isVoid_dec _    := inr _.
*)

Lemma isVoid_fun_correct t : boolSpec (isVoid_fun t) (isVoid t).
Proof. destruct t; my_auto. Qed.

Instance isVoid_dec t : Decision (isVoid t) := boolSpec_Decision (isVoid_fun_correct t).

(* Equations
isPointer_dec t : Decision (isPointer t) :=
isPointer_dec (Pointer _ _) := inl (IsPointer _ _);
isPointer_dec _             := inr _.
*)

Lemma isPointer_fun_correct t : boolSpec (isPointer_fun t) (isPointer t).
Proof. destruct t; my_auto. Qed.

Instance isPointer_dec t : Decision (isPointer t) := boolSpec_Decision (isPointer_fun_correct t).

(* Equations
isBool_dec it : Decision (isBool it) :=
isBool_dec Bool := inl IsBool;
isBool_dec _    := inr _.
*)

Lemma isBool_fun_correct t : boolSpec (isBool_fun t) (isBool t).
Proof. destruct t; my_auto. Qed.

Instance isBool_dec t : Decision (isBool t) := boolSpec_Decision (isBool_fun_correct t).

(* Equations
isSigned_dec P it : Decision (isSigned P it) :=
isSigned_dec P (Signed _) := inl (IsSignedInt P _) ;
isSigned_dec P Char with decide (Implementation.isCharSigned P) true := {
 | inl E  := inl (IsSignedChar P E) ;
 | inr _  := inr _};
isSigned_dec P _ := inr _.
Next Obligation. destruct it; my_auto. Qed.
*)

Lemma isSigned_fun_correct P it : boolSpec (isSigned_fun P it) (isSigned P it).
Proof.
  unfold_goal.
  set (isSigned_Bool P).
  set (isSigned_Signed P).
  set (isSigned_Unsigned P).
  destruct it; my_auto.
Qed.

Instance isSigned_dec P it : Decision (isSigned P it) := boolSpec_Decision (isSigned_fun_correct P it).

Lemma isSigned_incl {P} {it} : isSignedType it -> isSigned P it.
Proof. inversion 1; my_auto. Qed.

(* Equations
isSignedType_dec it : Decision (isSignedType it) :=
isSignedType_dec (Signed _) := inl (IsSignedType _) ;
isSignedType_dec _          := inr _                .
*)

Lemma isSignedType_fun_correct it : boolSpec (isSignedType_fun it) (isSignedType it).
Proof. do 2 unfold_goal; my_auto. Qed.

Instance isSignedType_dec it : Decision (isSignedType it) := boolSpec_Decision (isSignedType_fun_correct it).

(* Equations
isUnsigned_dec P it : Decision (isUnsigned P it) :=
isUnsigned_dec P (Unsigned _) := inl (IsUnsignedInt P _)   ;
isUnsigned_dec P Bool         := inl (IsUnsignedBool P)    ;
isUnsigned_dec P Char
  with decide (Implementation.isCharSigned P) true := {
  | inl _ := inr _                     ;
  | inr _ := inl (IsUnsignedChar P _) };
isUnsigned_dec P _ := inr _ .
Next Obligation. destruct it; my_auto. Qed.
*)

Lemma isUnsigned_fun_correct P it : boolSpec (isUnsigned_fun P it) (isUnsigned P it).
Proof.
  do 3 unfold_goal.
  set (isSigned_Bool P).
  set (isSigned_Signed P).
  set (isSigned_Unsigned P).
  destruct it; my_auto.
Qed.

Instance isUnsigned_dec P it : Decision (isUnsigned P it) := boolSpec_Decision (isUnsigned_fun_correct P it).

Lemma isUnsigned_incl {P} {it} : isUnsignedType it -> isUnsigned P it.
Proof. inversion 1; my_auto. Qed.

(* Equations
isUnsignedType_dec it : Decision (isUnsignedType it) :=
isUnsignedType_dec (Unsigned _) := inl (IsUnsignedTypeInt _) ;
isUnsignedType_dec Bool         := inl (IsUnsignedTypeBool)  ;
isUnsignedType_dec _            := inr _                     .
*)

Lemma isUnsignedType_fun_correct it : boolSpec (isUnsignedType_fun it) (isUnsignedType it).
Proof. do 3 unfold_goal; my_auto. Qed.

Instance isUnsignedType_dec it : Decision (isUnsignedType it) := boolSpec_Decision (isUnsignedType_fun_correct it).

Lemma integerTypeRange_precision_Signed P it1 it2 :
  isSigned P it1 ->
  isSigned P it2 ->
  precision P it1 <= precision P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2).
Proof.
  inversion 1;
  inversion 1; subst;
  match goal with
  | [|- le (integerTypeRange P Char) (integerTypeRange P Char)] =>
      constructor; omega
  | _ =>
      constructor;
      unfold integerTypeRange;
      unfold isUnsigned_fun;
      rewrite_all isSigned_Signed;
      match goal with 
      | [ H : isSigned_fun P Char = true |- _] => unfold isUnsigned_fun; rewrite H
      | _ => idtac
      end;
      destruct (binMode P); simpl;
      repeat rewrite max_mkRange; 
      repeat rewrite min_mkRange; 
      solve
        [ apply Z.sub_le_mono;
          [apply Z.pow_le_mono_r|]; omega
        | apply (proj1 (Z.opp_le_mono _ _));
          apply Z.pow_le_mono_r; omega
        | apply Z.add_le_mono; [|omega];
          apply (proj1 (Z.opp_le_mono _ _));
          apply Z.pow_le_mono_r; omega]
  end.
Qed.

Lemma integerTypeRange_precision_Signed_inv P it1 it2 :
  isSigned P it1 ->
  isSigned P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2) ->
  precision P it1 <= precision P it2.
Proof.
  set (precision_ge_one P it1).
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1;
  subst;
  match goal with
  | [ H : max (_ _ ?it1) <= max (_ _ ?it2) |- _] =>
      unfold integerTypeRange    in H;
      unfold isUnsigned_fun      in H;
      repeat rewrite (isSigned_Signed P) in H;
      match goal with 
      | [ R : isSigned_fun P Char = true |- _] => repeat rewrite R in H; simpl in H
      | _ => idtac
      end;
      destruct (binMode P); simpl in H;
      repeat rewrite max_mkRange in H;
      apply (Z.le_le_sub_lt 1 1 _ _ (Z.le_refl 1)) in H;
      apply (Z.le_le_sub_lt 1 1 _ _ (Z.le_refl 1));
      apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma integerTypeRange_precision_Unsigned P it1 it2 :
  isUnsigned P it1 ->
  isUnsigned P it2 ->
  precision P it1 <= precision P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2).
Proof.
  inversion 1;
  inversion 1; subst;
  constructor;
  unfold integerTypeRange;
  unfold isUnsigned_fun;
  repeat rewrite (isSigned_Unsigned P);
  repeat rewrite (isSigned_Bool     P);
  match goal with 
  | [ H : isSigned_fun P Char <> true |- _] => unfold isUnsigned_fun; rewrite_all (not_true_is_false _ H)
  | _ => idtac
  end;
  simpl;
  repeat rewrite max_mkRange;
  repeat rewrite min_mkRange;
  solve
    [ apply Z.sub_le_mono  ; [|omega];
      apply Z.pow_le_mono_r;   omega
    | omega].
Qed.

Lemma integerTypeRange_precision_Unsigned_inv P it1 it2 :
  isUnsigned P it1 ->
  isUnsigned P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2) ->
  precision P it1 <= precision P it2.
Proof.
  set (precision_ge_one P it1).
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [ H : max (_ _ ?it1) <= max (_ _ ?it2) |- _] =>
      unfold integerTypeRange    in H;
      unfold isUnsigned_fun      in H;
      repeat rewrite (isSigned_Unsigned P) in H;
      repeat rewrite (isSigned_Bool     P) in H;
      match goal with 
      | [ R : isSigned_fun P Char <> true |- _] => repeat rewrite (not_true_is_false _ R) in H; simpl in H
      | _ => idtac
      end;
      simpl in H;
      repeat rewrite max_mkRange in H;
      apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma precision_signed_ge_two {P} {it} : isSigned P it -> 2 <= precision P it.
Proof.
  destruct 1;
  match goal with
  | [H : isSigned_fun ?P Char = true |- _] =>
      let Hprec := fresh in
      let Hmin := fresh in
      set (precision_Char P) as Hprec; rewrite H in Hprec; simpl in Hprec;
      set (minPrecision_Signed P Ichar) as Hmin; simpl in Hmin
  | [|- _ <= precision ?P _] =>
      let Hmin := fresh in
      set (minPrecision_Signed P ibt) as Hmin; destruct ibt; simpl in Hmin
  end; omega.
Qed.

Lemma integerTypeRange_precision_Signed_Unsigned P it1 it2 :
  isSigned   P it1 ->
  isUnsigned P it2 ->
  neg(le (integerTypeRange P it1) (integerTypeRange P it2)).
Proof.
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [ H : isSigned _ _ |- _] =>
      set (precision_signed_ge_two H)
  end;
  match goal with
  | [ H : min (integerTypeRange P _) <= min (integerTypeRange P _) |- _] =>
      repeat destruct_integerBaseType;
      unfold integerTypeRange in H;
      unfold isUnsigned_fun in H;
      repeat rewrite (isSigned_Signed   P) in H;
      repeat rewrite (isSigned_Unsigned P) in H;
      repeat rewrite (isSigned_Bool     P) in H;      
      match goal with 
      | [ R : isSigned_fun P Char  = true |- _] => rewrite_all R
      | [ R : isSigned_fun P Char <> true |- _] => rewrite_all (not_true_is_false _ R)
      | _ => idtac
      end;
      destruct (binMode P);
      simpl in H;
      repeat rewrite min_mkRange in H
  end;
  match goal with
  | [ H : true <> true |- False] =>
      apply H; reflexivity
  | [ H : 0 <= - 2 ^ (precision P ?it - 1) |- _] =>
      rewrite <- Z.opp_0 in H;
      apply Z.opp_le_mono in H;
      set (integerTypeRange_signed_upper (precision_ge_one P it));
      omega
  | [ H : 0 <= - 2 ^ (precision P _ - 1) + 1 |- _] =>
      apply (Z.sub_le_mono_r _ _ 1) in H;
      rewrite <- Z.add_sub_assoc in H;
      rewrite Z.sub_diag in H;
      rewrite Z.sub_0_l in H;
      rewrite Zplus_0_r in H;
      rewrite <- (Z.pow_0_r 2) in H at 1;
      apply (proj2 (Z.opp_le_mono _ _)) in H;
      apply Z.pow_le_mono_r_iff in H; omega
  end.
Qed.

Lemma integerTypeRange_precision_Unsigned_Signed P it1 it2 :
  isUnsigned P it1 ->
  isSigned   P it2 ->
  precision P it1 < precision P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2).
Proof.
  inversion 1;
  inversion 1; subst;
  constructor;
  unfold integerTypeRange;
  unfold isUnsigned_fun;
  repeat rewrite (isSigned_Signed   P);
  repeat rewrite (isSigned_Unsigned P);
  repeat rewrite (isSigned_Bool     P);
  match goal with 
  | [ R    : isSigned_fun ?P =  true
    , notR : isSigned_fun ?P <> true |- _] => destruct (notR R)
  | [ R : isSigned_fun P Char  = true |- _] => rewrite_all R                      ; simpl
  | [ R : isSigned_fun P Char <> true |- _] => rewrite_all (not_true_is_false _ R); simpl
  | _ => idtac
  end;
  destruct (binMode P); simpl;
  match goal with
  | [|- min _ <= min _ ] =>
      repeat rewrite min_mkRange;
      solve [
          apply integerTypeRange_signed_lower1; apply precision_ge_one
        | apply integerTypeRange_signed_lower2; apply precision_ge_one
        | omega ]
  | [|- max _ <= max _ ] =>
      repeat rewrite max_mkRange;
      apply Z.sub_le_mono_r;
      apply Z.pow_le_mono_r; omega
  end.
Qed.

Lemma integerTypeRange_precision_Unsigned_Signed_inv P it1 it2 :
  isUnsigned P it1 ->
  isSigned   P it2 ->
  le (integerTypeRange P it1) (integerTypeRange P it2) ->
  precision P it1 < precision P it2.
Proof.
  set (precision_ge_one P it2).
  inversion 1;
  inversion 1;
  inversion 1; subst;
  match goal with
  | [H : max _ <= max _|- _] =>
    unfold integerTypeRange in H;
    unfold isUnsigned_fun   in H;
    repeat rewrite (isSigned_Signed   P) in H;
    repeat rewrite (isSigned_Unsigned P) in H;
    repeat rewrite (isSigned_Bool     P) in H;
    match goal with 
    | [ R    : isSigned_fun P Char =  true
      , notR : isSigned_fun P Char <> true |- _] => destruct (notR R)
    | [ R    : isSigned_fun P Char  = true |- _] => rewrite R                       in H; simpl in H
    | [ R    : isSigned_fun P Char <> true |- _] => rewrite (not_true_is_false _ R) in H; simpl in H
    | _ => idtac
    end;
    destruct (binMode P); simpl in H;
    repeat rewrite max_mkRange in H;
    apply (proj2 (Z.sub_le_mono_r _ _ 1)) in H;
    apply Z.lt_le_pred;
    rewrite <- Z.sub_1_r;
    apply (Z.pow_le_mono_r_iff 2); omega
  end.
Qed.

Lemma integerTypeRange_precision_Unsigned_Signed_eq P ibt :
  neg (precision P (Unsigned ibt) = precision P (Signed ibt)) ->
  neg (le (integerTypeRange P (Unsigned ibt)) (integerTypeRange P (Signed ibt))).
Proof.
  intros Hneq HleRange.
  assert (neg (precision P (Unsigned ibt) < precision P (Signed ibt))) as Hnlt.
    apply (Zle_not_lt _ _ (lePrecision_Signed_Unsigned P ibt)).
  exact (Hnlt (integerTypeRange_precision_Unsigned_Signed_inv P _ _ (IsUnsignedInt P ibt) (IsSignedInt P ibt) HleRange)).
Qed.

(* Equations
inIntegerTypeRange_dec P n it : Decision (inIntegerTypeRange P n it) :=
inIntegerTypeRange_dec P n it with mem_dec (Z_of_nat n) (integerTypeRange P it) := {
  | inl M := inl (InIntegerTypeRange P n it M)  ;
  | inr _ := inr _                      };
inIntegerTypeRange_dec P n _ := inr _.
*)

Lemma inIntegerTypeRange_fun_correct P n it : boolSpec (inIntegerTypeRange_fun P n it) (inIntegerTypeRange P n it).
Proof.
  do 2 unfold_goal.
  set (memNat_fun_correct n (integerTypeRange P it)).
  my_auto' fail ltac:(progress boolSpec_simpl).
Qed.

(* Equations
leIntegerTypeRange_dec P it1 it2 : Decision (leIntegerTypeRange P it1 it2) :=
leIntegerTypeRange_dec P it1 it2 with le_dec (integerTypeRange P it1) (integerTypeRange P it2) := {
  | inl L := inl (LeIntegerTypeRange P it1 it2 L) ;
  | inr _ := inr _                               };
leIntegerTypeRange_dec _ _ _ := inr _.
*)

Lemma leIntegerTypeRange_fun_correct P it1 it2 : boolSpec (leIntegerTypeRange_fun P it1 it2) (leIntegerTypeRange P it1 it2).
Proof.
  do 2 unfold_goal.
  set (isUnsigned_fun_correct P it1) as Hunsigned1.
  set (isUnsigned_fun_correct P it2) as Hunsigned2.
  set (isSigned_fun_correct   P it1) as Hsigned1.
  set (isSigned_fun_correct   P it2) as Hsigned2.
  destruct_integerType;
  unfold isUnsigned_fun in *;
  rewrite_all (isSigned_Signed   P);
  rewrite_all (isSigned_Unsigned P);
  rewrite_all (isSigned_Bool     P);
  match goal with
  | [|- context [Char]] =>
      let Heq := fresh in
      set (precision_Char P);
      case_eq (isSigned_fun P Char);
      intros Heq; repeat rewrite Heq in *
  | _ => idtac
  end; simpl;
  match goal with
  | [|- context[Z.ltb ?x ?y] ] =>
      let Heq := fresh in
      set (Zltb_correct x y);
      case_eq (Z.ltb x y); intros Heq; rewrite Heq in *; clear Heq
  | [|- context[Z.eqb ?x ?y] ] =>
      let Heq := fresh in
      set (Zeqb_correct x y);
      case_eq (Z.eqb x y); intros Heq; rewrite Heq in *; clear Heq
  | _ => idtac
  end; boolSpec_simpl; simpl;
  match goal with
  | [|- leIntegerTypeRange _ ?it ?it ] =>
      constructor; constructor; apply Z.le_refl
  | [ Hunsigned1 : isUnsigned ?P ?it1, Hunsigned2 : isUnsigned ?P ?it2 |- leIntegerTypeRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integerTypeRange_precision_Unsigned P it1 it2 Hunsigned1 Hunsigned2);
      set (lePrecision_Unsigned_Long_LongLong P);
      set (lePrecision_Unsigned_Int_Long      P);
      set (lePrecision_Unsigned_Short_Int     P);
      set (lePrecision_Unsigned_Ichar_Short   P);
      set (lePrecision_Unsigned_Bool_Ichar    P);
      omega
  | [ Hunsigned1 : isUnsigned ?P ?it1, Hunsigned2 : isUnsigned ?P ?it2 |- neg (leIntegerTypeRange ?P ?it1 ?it2) ] =>
      inversion 1; subst;
      match goal with
      | [H : le _ _ |- _] => set (integerTypeRange_precision_Unsigned_inv _ _ _ Hunsigned1 Hunsigned2 H)
      end;
      set (lePrecision_Unsigned_Long_LongLong P);
      set (lePrecision_Unsigned_Int_Long      P);
      set (lePrecision_Unsigned_Short_Int     P);
      set (lePrecision_Unsigned_Ichar_Short   P);
      set (lePrecision_Unsigned_Bool_Ichar    P);
      match goal with
      | [ H : neg (_ = _) |- _ ] => apply H
      end;
      omega
  | [ Hsigned1 : isSigned ?P ?it1, Hsigned2 : isSigned ?P ?it2 |- leIntegerTypeRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integerTypeRange_precision_Signed P it1 it2 Hsigned1 Hsigned2);
      set (lePrecision_Signed_Long_LongLong P);
      set (lePrecision_Signed_Int_Long      P);
      set (lePrecision_Signed_Short_Int     P);
      set (lePrecision_Signed_Ichar_Short   P);
      omega
  | [ Hsigned1 : isSigned ?P ?it1, Hsigned2 : isSigned ?P ?it2 |- neg (leIntegerTypeRange ?P ?it1 ?it2) ] =>
      inversion 1; subst;
      match goal with
      | [H : le _ _ |- _] => set (integerTypeRange_precision_Signed_inv _ _ _ Hsigned1 Hsigned2 H)
      end;
      set (lePrecision_Signed_Long_LongLong P);
      set (lePrecision_Signed_Int_Long      P);
      set (lePrecision_Signed_Short_Int     P);
      set (lePrecision_Signed_Ichar_Short   P);
      match goal with
      | [ H : neg (_ = _) |- _ ] => apply H
      end;
      omega
  | [ Hsigned1 : isSigned ?P ?it1, Hunsigned2 : isUnsigned ?P ?it2 |- neg (leIntegerTypeRange ?P ?it1 ?it2) ] =>
      set (integerTypeRange_precision_Signed_Unsigned P it1 it2 Hsigned1 Hunsigned2);
      inversion 1; contradiction
  | [ Hunsigned1 : isUnsigned ?P ?it1, Hsigned2 : isSigned ?P ?it2 |- neg (leIntegerTypeRange ?P ?it1 ?it2) ] =>
      inversion 1; subst;
      match goal with
      | [H : le _ _ |- _] => set (integerTypeRange_precision_Unsigned_Signed_inv _ _ _ Hunsigned1 Hsigned2 H)
      end;
      match it1 with
      | Unsigned ?ibt => set (lePrecision_Signed_Unsigned P ibt)
      | _ => idtac
      end;
      set (lePrecision_Signed_Unsigned_Ichar  P);
      set (lePrecision_Unsigned_Long_LongLong P);
      set (lePrecision_Unsigned_Int_Long      P);
      set (lePrecision_Unsigned_Short_Int     P);
      set (lePrecision_Unsigned_Ichar_Short   P);
      set (lePrecision_Unsigned_Bool_Ichar    P);
      solve [ contradiction | omega]
  | [ Hunsigned1 : isUnsigned ?P ?it1, Hsigned2 : isSigned ?P ?it2 |- leIntegerTypeRange ?P ?it1 ?it2 ] =>
      constructor;
      apply (integerTypeRange_precision_Unsigned_Signed P it1 it2 Hunsigned1 Hsigned2); assumption
  end.
Qed.

Instance leIntegerTypeRange_dec P : DecidableRelation (leIntegerTypeRange P) := {
  decide it1 it2 := boolSpec_Decision (leIntegerTypeRange_fun_correct P it1 it2)
}.

Instance eqIntegerRankBase_irrefl : Irreflexive eqIntegerRankBase.
Proof. inversion 1. Qed.

(* Equations
eqIntegerRankBase_dec it1 it2 : Decision (eqIntegerRankBase it1 it2) :=
eqIntegerRankBase_dec (Signed ibt1) (Unsigned ibt2) with decide ibt1 ibt2 := {
  | inl eq_refl := inl (EqIntegerRankBaseUnsigned _)  ;
  | inr _       := inr _                             };
eqIntegerRankBase_dec Char          (Unsigned  Ichar) := inl EqIntegerRankBaseUnsignedChar  ;
eqIntegerRankBase_dec Char          (Signed    Ichar) := inl EqIntegerRankBaseSignedChar    ;
eqIntegerRankBase_dec _              _                := inr _                              .

Next Obligation.
  intros.
  repeat match goal with
  | [ it  : integerType     |- _ ] => destruct it
  | [ ibt : integerBaseType |- _ ] => destruct ibt
  end; my_auto.
Qed.
*)

Lemma eqIntegerRankBase_fun_correct it1 it2 : boolSpec (eqIntegerRankBase_fun it1 it2) (eqIntegerRankBase it1 it2).
Proof. do 2 unfold_goal; my_auto. Qed.

Instance eqIntegerRankBase_DecR : DecidableRelation eqIntegerRankBase := {
  decide it1 it2 := boolSpec_Decision (eqIntegerRankBase_fun_correct it1 it2)
}.

Ltac eqIntegerRankBase_false :=
  match goal with
  | [ H : eqIntegerRankBase ?a ?b |- _ ] => inversion H; congruence
  end.

Ltac eqIntegerRank_finish :=
  solve [ eqIntegerRankBase_false 
        | apply EqIntegerRankSym; my_auto
        | intros; apply EqIntegerRankRefl].
Ltac eqIntegerRank_tac := my_auto' eqIntegerRank_finish fail.

Lemma eqIntegerRank_dec_aux it1 it2 : eqIntegerRankBase it1 it2 + eqIntegerRankBase it2 it1 + (it1 = it2) + neg (eqIntegerRank it1 it2).
Proof.
  destruct (decide it1 it2 : Decision (it1 = it2)).
  - left; right; assumption.
  - destruct (decide it1 it2 : Decision (eqIntegerRankBase it1 it2)).
    + left; left; left; assumption.
    + destruct (decide it2 it1 : Decision (eqIntegerRankBase it2 it1)).
      * left; left; right; assumption.
      * right; my_auto.
Qed.

(* Equations
eqIntegerRank_dec it1 it2 : Decision (eqIntegerRank it1 it2) :=
eqIntegerRank_dec it1 it2 with eqIntegerRank_dec_aux it1 it2 := {
  | inl (inl (inl b)) := inl (EqIntegerRankBase _ _ b) ;
  | inl (inl (inr s)) := inl (EqIntegerRankSym  _ _ s) ;
  | inl (inr eq_refl) := inl (EqIntegerRankRefl     _) ;
  | inr N             := inr N
}.
*)

Lemma eqIntegerRank_fun_correct it1 it2 : boolSpec (eqIntegerRank_fun it1 it2) (eqIntegerRank it1 it2).
Proof.
  do 2 unfold_goal.
  repeat match goal with
  | [ |- context[eqIntegerRankBase_fun ?it1 ?it2] ] =>
      set (eqIntegerRankBase_fun_correct it1 it2); boolSpec_destruct 
  end;
  eqIntegerRank_tac.
Qed.

Instance eqIntegerRank_DecR : DecidableRelation eqIntegerRank := {
  decide it1 it2 := boolSpec_Decision (eqIntegerRank_fun_correct it1 it2)
}.

Instance eqIntegerRank_trans : Transitive eqIntegerRank.
Proof.
  intros it1 it it2.
  generalize (eqIntegerRank_dec_aux it1 it);
  generalize (eqIntegerRank_dec_aux it it2);
  destruct_sum; eqIntegerRank_tac;
  repeat (
    match goal with
    | [ it : integerType |- _ ] => destruct it
    | [ ibt1 : integerBaseType , ibt2 : integerBaseType |- context[_ : eqIntegerRank (Signed ?ibt1) (Unsigned ?ibt2)] ]
        => notHyp (neg (ibt1 = ibt2)); notHyp (ibt1 = ibt2);
           destruct (decide ibt1 ibt2 : Decision (ibt1 = ibt2))
    | [ |- (eqIntegerRank _ _) -> _ ] => inversion 1
    | [ ibt : integerBaseType |- _ ] => destruct ibt
    end; eqIntegerRank_tac).
Qed.

Instance eqIntegerRank_sym : Symmetric eqIntegerRank.
Proof. inversion 1; eqIntegerRank_tac. Qed.

Instance eqIntegerRank_equiv : Equivalence eqIntegerRank := {
  Equivalence_Reflexive  := EqIntegerRankRefl   ;
  Equivalence_Symmetric  := eqIntegerRank_sym   ;
  Equivalence_Transitive := eqIntegerRank_trans
}.

Instance ltIntegerRankBase_irrefl {P} : Irreflexive (ltIntegerRankBase P).
Proof. generalize Z.lt_irrefl; inversion 2; my_auto; intuition. Qed.

Ltac precision_tac :=
  match goal with
  | [P : impl, _ : _ < _ |- _ ] =>
      generalize (lePrecision_Signed_Ichar_Short    P); 
      generalize (lePrecision_Signed_Short_Int      P);
      generalize (lePrecision_Signed_Int_Long       P);
      generalize (lePrecision_Signed_Long_LongLong  P);
      omega
  | _ => idtac
  end.

Instance ltIntegerRankBase_asymm {P} : Asymmetric (ltIntegerRankBase P).
Proof. intros; inversion 1; inversion 1; my_auto; precision_tac; intuition. Qed.

Lemma ltIntegerRankBase_least P it : neg (ltIntegerRankBase P it Bool).
Proof. inversion 1; intuition. Qed.

(* Equations
ltIntegerRankBase_dec P it1 it2 : Decision (ltIntegerRankBase P it1 it2) :=
ltIntegerRankBase_dec P Bool it with isBool_dec it := {
  | inl _ := inr _                               ;
  | inr N := inl (LtIntegerRankBaseBool P it N) };
ltIntegerRankBase_dec P (Signed  Long) (Signed LongLong) := inl (LtIntegerRankBaseLongLong P) ;
ltIntegerRankBase_dec P (Signed   Int) (Signed     Long) := inl (LtIntegerRankBaseLong     P) ;
ltIntegerRankBase_dec P (Signed Short) (Signed      Int) := inl (LtIntegerRankBaseInt      P) ;
ltIntegerRankBase_dec P (Signed Ichar) (Signed    Short) := inl (LtIntegerRankBaseShort    P) ;
ltIntegerRankBase_dec P (Signed  ibt1) (Signed     ibt2)
  with Z_lt_dec (precision P (Signed ibt1)) (precision P (Signed ibt2)) := {
  | left  L := inl (LtIntegerRankBasePrecision P _ _ L)  ;
  | right _ := inr _                                    };
ltIntegerRankBase_dec P _ _ := inr _.
*)

Ltac ltIntegerRankBase_tac :=
  match goal with
  | [ |- ltIntegerRankBase ?P (Signed  Long) (Signed LongLong) ] => exact (LtIntegerRankBaseLongLong P)
  | [ |- ltIntegerRankBase ?P (Signed   Int) (Signed     Long) ] => exact (LtIntegerRankBaseLong     P)
  | [ |- ltIntegerRankBase ?P (Signed Short) (Signed      Int) ] => exact (LtIntegerRankBaseInt      P)
  | [ |- ltIntegerRankBase ?P (Signed Ichar) (Signed    Short) ] => exact (LtIntegerRankBaseShort    P)
  end.

Lemma ltIntegerRankBase_fun_correct P it1 it2 : boolSpec (ltIntegerRankBase_fun P it1 it2) (ltIntegerRankBase P it1 it2).
Proof.
  do 2 unfold_goal; my_auto; intros;
  match goal with
(*
  | [ H : negb (isBool_fun ?it) = ?b |- _] =>
      let Hcorrect := fresh in
      match b with
      | true  => rewrite negb_true_iff  in H
      | false => rewrite negb_false_iff in H
      end;
      set (isBool_fun_correct it2) as Hcorrect;
      rewrite H in Hcorrect
*)
  | [ H : Z.ltb ?z ?z = true  |- _ ] => rewrite Z.ltb_irrefl in H
  | [ H : Z.ltb ?x ?y = true  |- _ ] => set (proj1 (Z.ltb_lt  x y) H)
  | [ H : Z.ltb ?x ?y = false |- _ ] => set (proj1 (Z.ltb_nlt x y) H)
  | _ => ltIntegerRankBase_tac
  end; my_auto.
Qed.

Instance ltIntegerRankBase_DecR P : DecidableRelation (ltIntegerRankBase P) := {
  decide it1 it2 := boolSpec_Decision (ltIntegerRankBase_fun_correct P it1 it2)
}.

Ltac ltIntegerRankCongruence_destruct :=
  match goal with
  | [ H : eqIntegerRank     _ _ |- _ ] => inversion H; clear H
  | [ H : eqIntegerRankBase _ _ |- _ ] => inversion H; clear H
  | [ H : ltIntegerRankBase _  _  (Unsigned _) |- _ ] => inversion H; clear H
  | [ H : ltIntegerRankBase _  _  Char |- _ ] => inversion H; clear H
  end.

Ltac ltIntegerRankCongruence_finish :=
  match goal with
  | [ H : ltIntegerRankBase _  _   _    |- _     ] => now inversion H
  | [ H : ltIntegerRankBase ?P ?it Bool |- _     ] => destruct (ltIntegerRankBase_least P it H)
  | [ H : ltIntegerRankBase _  ?x  ?x   |- False ] => exact (ltIntegerRankBase_irrefl x H)
(*
TODO Coq can't find instance for
  exact (irreflexive x H)
*)
  | [ H1 : ltIntegerRankBase _ ?x ?y , H2 : ltIntegerRankBase _ ?y ?x |- False ] => exact (ltIntegerRankBase_asymm x y H1 H2)
(*
TODO Coq can't find instance for
  exact (asymmetric x y H1 H2)
*)
  end.

Ltac ltIntegerRankCongruence_tac := repeat (ltIntegerRankCongruence_destruct; my_auto); try ltIntegerRankCongruence_finish; my_auto.

(*
Ltac ltIntegerRankCongruence_finish :=
  repeat (match goal with
  | [ H : eqIntegerRank     _ _ |- _ ] => inversion H; clear H
  | [ H : eqIntegerRankBase _ _ |- _ ] => inversion H; clear H
  | [ H : ltIntegerRankBase _  _  _ |- _ ] => now inversion H
  | [ H : ltIntegerRankBase ?P ?it Bool |- _ ] => destruct (ltIntegerRankBase_least P it H)
  | [ H : ltIntegerRankBase _  _  (Unsigned _) |- _ ] => inversion H; clear H
  | [ H : ltIntegerRankBase _  _  Char |- _ ] => inversion H; clear H
  | [ H : ltIntegerRankBase _ ?x ?x |- False ] => exact (irreflexive x H)
  | [ H1 : ltIntegerRankBase _ ?x ?y , H2 : ltIntegerRankBase _ ?y ?x |- False ] => exact (asymmetric x y H1 H2)
  end; my_auto); my_auto.
*)

Instance ltIntegerRankCongruence_irrefl {P} : Irreflexive (ltIntegerRankCongruence P).
Proof. inversion 1; ltIntegerRankCongruence_tac. Qed.

Instance ltIntegerRankCongruence_asymm {P} : Asymmetric (ltIntegerRankCongruence P).
Proof. intros ? ?; inversion 1; inversion 1; ltIntegerRankCongruence_tac. Qed.

Definition ltIntegerRankCongruence_incl {P} {it1 it2} : ltIntegerRankBase P it1 it2 -> ltIntegerRankCongruence P it1 it2.
Proof.
  intros; econstructor.
  - apply EqIntegerRankRefl.
  - apply EqIntegerRankRefl.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned_Unsigned {P} {ibt1} {ibt2} :
  ltIntegerRankBase P (Signed ibt1) (Signed ibt2) ->
  ltIntegerRankCongruence P (Unsigned ibt1) (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor; constructor.
  - constructor; constructor.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned1 {P} {ibt1} {it2} :
  ltIntegerRankBase P (Signed ibt1) it2 ->
  ltIntegerRankCongruence P (Unsigned ibt1) it2.
Proof.
  intros.
  econstructor.
  - constructor; constructor.
  - constructor 3.
  - assumption.
Qed.

Lemma ltIntegerRankCongruence_Unsigned2 {P} {it1} {ibt2} :
  ltIntegerRankBase P it1 (Signed ibt2) ->
  ltIntegerRankCongruence P it1 (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor 3.
  - constructor; constructor.
  - assumption.
Qed.

Lemma ltIntegerRankBaseCongruence_Char1 {P} {it2} :
  ltIntegerRankBase P (Signed Ichar) it2 ->
  ltIntegerRankCongruence P Char it2.
Proof.
  intros.
  econstructor.
  - constructor 2. constructor 3.
  - constructor 3.
  - assumption.
Qed.

Lemma ltIntegerRankBaseCongruence_Char_Unsigned {P} {ibt2} :
  ltIntegerRankBase P (Signed Ichar) (Signed ibt2) ->
  ltIntegerRankCongruence P Char (Unsigned ibt2).
Proof.
  intros.
  econstructor.
  - constructor 2. constructor 3.
  - constructor 1; constructor 1.
  - assumption.
Qed.

Ltac ltIntegerRankCongruence_dec_tac :=
  ltIntegerRankCongruence_tac;
  try solve
    [ inversion 1; ltIntegerRankCongruence_tac
    | unfold neg; intros; apply_ctx; constructor; inversion 1
    | inversion 2; ltIntegerRankCongruence_tac
    | inversion 1; ltIntegerRankCongruence_tac;
      match goal with
      | [ H : ltIntegerRankBase _ (Signed ?ibt) (Signed Ichar) |- _ ] =>
          destruct ibt; inversion H;
          ltIntegerRankCongruence_tac;
          precision_tac;
          intuition
      end].

(*Equations
Obligation Tactic := ltIntegerRankCongruence_dec_tac.
Equations(noind nocomp)
ltIntegerRankCongruence_dec P it1 it2 : Decision (ltIntegerRankCongruence P it1 it2) :=
ltIntegerRankCongruence_dec P _    Bool := inr _ ;
ltIntegerRankCongruence_dec P Bool it2  := inl (ltIntegerRankCongruence_incl (LtIntegerRankBaseBool P it2 _)) ;
ltIntegerRankCongruence_dec P Char Char := inr _ ;
ltIntegerRankCongruence_dec P Char (Unsigned ibt2)
  with ltIntegerRankBase_dec P (Signed Ichar) (Signed ibt2) := {
     | inl Y := inl (ltIntegerRankBaseCongruence_Char_Unsigned Y) ;
     | inr N := inr (N ∘ _)    };
ltIntegerRankCongruence_dec P Char (Signed ibt2)
  with ltIntegerRankBase_dec P (Signed Ichar) (Signed ibt2) := {
     | inl Y := inl (ltIntegerRankBaseCongruence_Char1 Y) ;
     | inr N := inr (N ∘ _)    };
ltIntegerRankCongruence_dec P (Unsigned ibt1) Char := inr _;
ltIntegerRankCongruence_dec P (Signed   ibt1) Char := inr _;
ltIntegerRankCongruence_dec P (Unsigned ibt1) (Unsigned ibt2)
  with ltIntegerRankBase_dec P (Signed ibt1) (Signed ibt2) := {
     | inl Y := inl (ltIntegerRankCongruence_Unsigned_Unsigned Y)  ;
     | inr N := inr (N ∘ _) };
ltIntegerRankCongruence_dec P (Unsigned ibt1) it2 with (ltIntegerRankBase_dec P (Signed ibt1) it2) := {
  | inl Y := inl (ltIntegerRankCongruence_Unsigned1 Y)    ;
  | inr N := inr (N ∘ _) };
ltIntegerRankCongruence_dec P it1 (Unsigned ibt2) with (ltIntegerRankBase_dec P it1 (Signed ibt2)) := {
  | inl Y := inl (ltIntegerRankCongruence_Unsigned2 Y)    ;
  | inr N := inr (N ∘ _) };
ltIntegerRankCongruence_dec P it1 it2
  with ltIntegerRankBase_dec P it1 it2 := {
     | inl Y := inl (ltIntegerRankCongruence_incl Y) ;
     | inr _ := inr _}.
*)

Ltac ltIntegerRankCongruence_pos_tac tac :=
  match goal with
  | [ |- ltIntegerRankCongruence ?P Bool ?it2 ] => apply ltIntegerRankCongruence_incl; apply (LtIntegerRankBaseBool P it2); inversion 1
  | [ |- ltIntegerRankCongruence _ Char         (Signed   _) ] => apply ltIntegerRankBaseCongruence_Char1        ; tac
  | [ |- ltIntegerRankCongruence _ Char         (Unsigned _) ] => apply ltIntegerRankBaseCongruence_Char_Unsigned; tac
  | [ |- ltIntegerRankCongruence _ (Signed   _) (Signed   _) ] => apply ltIntegerRankCongruence_incl             ; tac
  | [ |- ltIntegerRankCongruence _ (Unsigned _) (Unsigned _) ] => apply ltIntegerRankCongruence_Unsigned_Unsigned; tac
  | [ |- ltIntegerRankCongruence _ (Unsigned _) (Signed   _) ] => apply ltIntegerRankCongruence_Unsigned1        ; tac
  | [ |- ltIntegerRankCongruence _ (Signed   _) (Unsigned _) ] => apply ltIntegerRankCongruence_Unsigned2        ; tac
  end.

Lemma ltIntegerRankCongruence_fun_correct P it1 it2 : boolSpec (ltIntegerRankCongruence_fun P it1 it2) (ltIntegerRankCongruence P it1 it2).
Proof.
  do 2 unfold_goal; destruct it1; destruct it2;
  repeat match goal with
  | [ |- context[ltIntegerRankBase_fun ?P ?it1 ?it2] ] =>
      set (ltIntegerRankBase_fun_correct P it1 it2);
      boolSpec_destruct
  | _ => ltIntegerRankCongruence_pos_tac assumption
  | _ => ltIntegerRankCongruence_dec_tac
  end.
Qed.

Instance ltIntegerRankCongruence_dec P : DecidableRelation (ltIntegerRankCongruence P) := {
  decide it1 it2 := boolSpec_Decision (ltIntegerRankCongruence_fun_correct P it1 it2)
}.

Ltac ltIntegerRank_pos_tac :=
  match goal with
  | [ |- ltIntegerRank _ _                _] =>
      apply LtIntegerRankBase;
      ltIntegerRankCongruence_pos_tac idtac;
      now ltIntegerRankBase_tac
  | [ |- ltIntegerRank _ Char             _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- ltIntegerRank _ (Signed   Ichar) _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- ltIntegerRank _ (Unsigned Ichar) _] => ltIntegerRank_pos_tac_iter (Signed    Short)
  | [ |- ltIntegerRank _ (Signed   Short) _] => ltIntegerRank_pos_tac_iter (Signed      Int)
  | [ |- ltIntegerRank _ (Unsigned Short) _] => ltIntegerRank_pos_tac_iter (Signed      Int)
  | [ |- ltIntegerRank _ (Signed     Int) _] => ltIntegerRank_pos_tac_iter (Signed     Long)
  | [ |- ltIntegerRank _ (Unsigned   Int) _] => ltIntegerRank_pos_tac_iter (Signed     Long)
  | [ |- ltIntegerRank _ (Signed    Long) _] => ltIntegerRank_pos_tac_iter (Signed LongLong)
  | [ |- ltIntegerRank _ (Unsigned  Long) _] => ltIntegerRank_pos_tac_iter (Signed LongLong)
  end
with ltIntegerRank_pos_tac_iter t :=
  apply (LtIntegerRankTransitive _ _ _ t);
  [ ltIntegerRankCongruence_pos_tac idtac; ltIntegerRankBase_tac
  | ltIntegerRank_pos_tac ].

Ltac ltIntegerRank_neg_tac :=
  match goal with
  | _ => contradiction
  | [ H  : ltIntegerRankCongruence _ ?x ?x |- False ] => exact (ltIntegerRankCongruence_irrefl x H)
  | [ H : ltIntegerRankCongruence _ _ _         |- _] => inversion H; ltIntegerRankCongruence_tac; clear H
  | [ ibt : integerBaseType                     |- _] => destruct ibt
  | [ it : integerType                          |- _] => destruct it
  | [ H : ltIntegerRankBase _ _ _               |- _] => ltIntegerRankCongruence_finish
  | [ H1 : precision ?P ?it1 < precision ?P ?it2, H2 : ltIntegerRankBase ?P ?it1 ?it2 |- _] => (now precision_tac) || (clear H1; clear H2)
  | [ H : ltIntegerRankBase _ _ _               |- _] => inversion H; now precision_tac
  | [ H : ltIntegerRankBase _ _ _               |- _] => clear H
  | [ H : ltIntegerRank _ _ _                   |- _] => inversion H; subst; clear H
  end.

Definition ltIntegerRank_neg_next it : option integerType :=
  match it with
  | Unsigned ibt    => Some (Signed ibt)
  | Signed LongLong => Some (Unsigned Long)
  | Signed Long     => Some (Unsigned Int)
  | Signed Int      => Some (Unsigned Short)
  | Signed Short    => Some (Unsigned Ichar)
  | Signed Ichar    => Some Char
  | Char            => Some Bool
  | Bool            => None
  end.

Ltac ltIntegerRank_neg_tac_next P it1 it2 :=
  let next := eval compute in (ltIntegerRank_neg_next it1) in
  assert (neg (ltIntegerRank P it1 it2)) by (clear_integerType; intros ?; now abstract (do 5 ltIntegerRank_neg_tac));
  match next with
  | Some ?it1' =>
      let eq      := eval compute in (eqIntegerRank_fun it1  it2) in
      let eq_next := eval compute in (eqIntegerRank_fun it1' it2) in
      match eval compute in (andb eq (negb eq_next)) with
      | true  => idtac
      | false => ltIntegerRank_neg_tac_next P it1' it2
      end
  | None => idtac
  end.

Lemma ltIntegerRank_fun_correct P it1 it2 : boolSpec (ltIntegerRank_fun it1 it2) (ltIntegerRank P it1 it2).
Proof.
  unfold_goal; scatter fail.
  - destruct_integerType; my_auto; ltIntegerRank_pos_tac.
  - destruct_integerType_hyp it2;
    abstract (
      match goal with
      | [ |- context[ltIntegerRank ?P ?H ?it2]] =>
          ltIntegerRank_neg_tac_next P (Unsigned LongLong) it2; destruct_integerType; my_auto
      end
    ).
Qed.

Instance ltIntegerRank_decR P : DecidableRelation (ltIntegerRank P) := {
  decide it1 it2 := boolSpec_Decision (ltIntegerRank_fun_correct P it1 it2)
}.

Instance ltIntegerRank_asymm P : Asymmetric (ltIntegerRank P).
Proof.
  intros x y ? ?.
  set (ltIntegerRank_fun_correct P x y).
  set (ltIntegerRank_fun_correct P y x).
  destruct_integerType;
  boolSpec_simpl;
  contradiction.
Qed.

Instance ltIntegerRank_irrefl P : Irreflexive (ltIntegerRank P) :=
  fun it H => ltIntegerRank_asymm P it it H H.

Instance ltIntegerRank_trans P : Transitive (ltIntegerRank P).
Proof.
  unfold Transitive; fix IH 4.
  inversion 1; subst.
  + econstructor 2; eassumption.
  +  match goal with
    | [ _ : ltIntegerRankCongruence ?P _ ?it1, H1 : ltIntegerRank ?P ?it1 ?it |- ltIntegerRank ?P ?it ?it2 -> _] =>
        let H2 := fresh in
        intros H2; set (IH it1 it it2 H1 H2)
    end.
    econstructor 2; eassumption.
Qed.

Lemma ltIntegerRank_cong1 P it1 it it2 : eqIntegerRank it1 it -> ltIntegerRank P it it2 -> ltIntegerRank P it1 it2.
Proof.
  inversion 2; subst;
  match goal with
  | [H : ltIntegerRankCongruence _ _ _ |- _] => inversion H; subst; clear H
  end;
  match goal with
  | [ E  : eqIntegerRank       ?it1 ?it
    , Eb : eqIntegerRank       ?itb ?it
    , Ee : eqIntegerRank       ?ite ?it2
    , L  : ltIntegerRankBase P ?itb ?ite |- ltIntegerRank ?P ?it1 _] =>
    set (LtIntegerRankCongruence _ _ _ _ _ (eqIntegerRank_trans _ _ _ Eb (eqIntegerRank_sym _ _ E)) Ee L)
  end.
  + constructor  1;  assumption.
  + econstructor 2; eassumption.
Qed.

Lemma ltIntegerRank_cong2 P :
  forall it1 it it2, eqIntegerRank it it2 -> ltIntegerRank P it1 it -> ltIntegerRank P it1 it2.
Proof.
  fix IH 5.
  inversion 2; subst.
  + match goal with
    | [H : ltIntegerRankCongruence _ _ _ |- _] => inversion H; subst; clear H
    end.
    match goal with
    | [ E  : eqIntegerRank       ?it ?it2
      , Eb : eqIntegerRank       ?itb ?it1
      , Ee : eqIntegerRank       ?ite _
      , L  : ltIntegerRankBase P ?itb ?ite |- ltIntegerRank ?P ?it1 ?it2] =>
        set (LtIntegerRankCongruence _ _ _ _ _ Eb (eqIntegerRank_trans _ _ _ Ee E) L)
    end; constructor 1; assumption.
  + match goal with
    | [ E  : eqIntegerRank ?it _
      , _ : ltIntegerRankCongruence ?P ?it1 ?itn
      , L : ltIntegerRank           ?P ?itn ?it  |- _] => set (IH _ _ _ E L); econstructor 2; eassumption
    end.
Qed.

Lemma leIntegerRank_fun_correct P it1 it2 : boolSpec (leIntegerRank_fun it1 it2) (leIntegerRank P it1 it2).
Proof.
  do 2 unfold_goal.
  set (eqIntegerRank_fun_correct   it1 it2).
  set (ltIntegerRank_fun_correct P it1 it2).
  my_auto' fail ltac:(idtac; boolSpec_destruct).
Qed.

Instance leIntegerRank_decR P : DecidableRelation (leIntegerRank P) := {
  decide it1 it2 := boolSpec_Decision (leIntegerRank_fun_correct P it1 it2)
}.

Instance leIntegerRank_refl P : Reflexive (leIntegerRank P).
Proof. intros ?; constructor; apply EqIntegerRankRefl. Qed.

Instance leIntegerRank_trans P : Transitive (leIntegerRank P).
Proof.
  inversion 1; inversion 1; my_auto.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong1; eassumption.
  + constructor 2; eapply ltIntegerRank_cong2; eassumption.
  + constructor 2; eapply ltIntegerRank_trans; eassumption.
Qed.

Lemma leIntegerRank_cong1 P it1 it it2 : eqIntegerRank it1 it -> leIntegerRank P it it2 -> leIntegerRank P it1 it2.
Proof.
  inversion 2; subst.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong1; eassumption.
Qed.

Lemma leIntegerRank_cong2 P it1 it it2 : eqIntegerRank it it2 -> leIntegerRank P it1 it -> leIntegerRank P it1 it2.
Proof.
  inversion 2; subst.
  + constructor 1; eapply eqIntegerRank_trans; eassumption.
  + constructor 2; eapply ltIntegerRank_cong2; eassumption.
Qed.

Lemma isArithmetic_fun_correct t : boolSpec (isArithmetic_fun t) (isArithmetic t).
Proof.
  do 2 unfold_goal.
  set (isInteger_fun_correct t).
  boolSpec_destruct; my_auto.
Qed.  

Instance isArithmetic_dec t : Decision (isArithmetic t) := boolSpec_Decision (isArithmetic_fun_correct t).

Lemma isScalar_fun_correct t : boolSpec (isScalar_fun t) (isScalar t).
Proof.
  do 2 unfold_goal.
  set (isPointer_fun_correct    t).
  set (isArithmetic_fun_correct t).
  my_auto' ltac:(constructor 2; assumption) ltac:(idtac; boolSpec_destruct).
Qed.

Instance isScalar_dec t : Decision (isScalar t) := boolSpec_Decision (isScalar_fun_correct t).

Lemma isArray_fun_correct t : boolSpec (isArray_fun t) (isArray t).
Proof. destruct t; my_auto. Qed.

Instance isArray_dec t : Decision (isArray t) := boolSpec_Decision (isArray_fun_correct t).

Lemma isFunction_fun_correct t : boolSpec (isFunction_fun t) (isFunction t).
Proof. destruct t; my_auto. Qed.

Instance isFunction_dec t : Decision (isFunction t) := boolSpec_Decision (isFunction_fun_correct t).

Lemma isCorrespondingUnsigned_fun_correct it1 it2 : boolSpec (isCorrespondingUnsigned_fun it1 it2) (isCorrespondingUnsigned it1 it2).
Proof. destruct it1; destruct it2; my_auto. Qed.

Instance isCorrespondingUnsigned_decR : DecidableRelation isCorrespondingUnsigned :=
  fun it1 it2 => boolSpec_Decision (isCorrespondingUnsigned_fun_correct it1 it2).

Lemma isCorrespondingUnsigned_find_correct it :
  match isCorrespondingUnsigned_find it with
  | Some it' => isCorrespondingUnsigned it it'
  | None     => forall it', neg (isCorrespondingUnsigned it it')
  end.
Proof. destruct it; my_auto. Qed.

Lemma isCorrespondingUnsigned_find_unique it1 it2 :
  isCorrespondingUnsigned it1 it2 ->
  isCorrespondingUnsigned_find it1 = Some it2.
Proof. destruct 1; reflexivity. Qed.

Lemma isIntegerPromotion_Signed_Unsigned {P} {it1} {it2} :
  isIntegerPromotion P it1 it2 ->
  (isSignedType it2 + isUnsignedType it2).
Proof.
  inversion 1;
  solve
    [ econstructor (constructor)
    | destruct it2;
      solve
        [ econstructor (constructor)
        | exfalso; unfold not in *; apply_ctx;
          set (ltIntegerRank_fun_correct P Char (Signed Int));
          my_auto
        ]
    ].
Qed.

Lemma isIntegerPromotion_fun_correct P it1 it2 : boolSpec (isIntegerPromotion_fun P it1 it2) (isIntegerPromotion P it1 it2).
Proof.
  do 2 unfold_goal.
  set (leIntegerRank_fun_correct      P it1 (Signed Int)).
  set (leIntegerTypeRange_fun_correct P it1 (Signed Int)).
  destruct_integerType;
  match goal with
  | [ |- isIntegerPromotion _ (Signed   Int) (Signed   Int) ] => apply IsIntegerPromotionSignedInt
  | [ |- isIntegerPromotion _ (Unsigned Int) (Unsigned Int) ] => apply IsIntegerPromotionUnsignedInt
  | _ => repeat boolSpec_destruct; my_auto
  end.
Qed.  

Lemma isIntegerPromotion_find_correct P it : isIntegerPromotion P it (isIntegerPromotion_find P it).
Proof.
  unfold_goal.
  set (leIntegerRank_fun_correct      P it (Signed Int)).
  set (leIntegerTypeRange_fun_correct P it (Signed Int)).
  destruct_integerType;
  match goal with
  | [ |- isIntegerPromotion _ (Signed   Int) (Signed   Int) ] => apply IsIntegerPromotionSignedInt
  | [ |- isIntegerPromotion _ (Unsigned Int) (Unsigned Int) ] => apply IsIntegerPromotionUnsignedInt
  | _ => repeat boolSpec_destruct; my_auto
  end.
Qed.

Lemma isIntegerPromotion_find_unique P it1 it2 : isIntegerPromotion P it1 it2 -> isIntegerPromotion_find P it1 = it2.
Proof.
  unfold_goal.
  set (leIntegerRank_fun_correct      P it1 (Signed Int)).
  set (leIntegerTypeRange_fun_correct P it1 (Signed Int)).
  destruct_integerType; boolSpec_destruct; my_auto.
Qed.

Lemma isUsualArithmeticInteger_fun_correct P it1 it2 it3 :
 boolSpec (isUsualArithmeticInteger_fun P it1 it2 it3)
          (isUsualArithmeticInteger     P it1 it2 it3).
Proof.
  do 2 unfold_goal.
  set (decide it1 it2 : Decision (it1 = it2)) as Heq.
  destruct Heq.
  - my_auto.
  - set (isSignedType_fun_correct it1) as Hsigned1_correct.
    set (isSignedType_fun_correct it2) as Hsigned2_correct.
    set (isUnsignedType_fun_correct it1) as Hunsigned1_correct.
    set (isUnsignedType_fun_correct it2) as Hunsigned2_correct.
    destruct it1; destruct it2;
    boolSpec_simpl;
    abstract (
    match goal with
    | [_ : isSignedType   ?it1, _ : isSignedType   ?it2 |- context[isUsualArithmeticInteger ?P ?it1 ?it2 _]] =>
        set (ltIntegerRank_fun_correct P it2 it1);
        set (ltIntegerRank_fun_correct P it1 it2);
        destruct_integerBaseType;
        boolSpec_simpl;
        destruct_decide;
        now my_auto
    | [_ : isUnsignedType ?it1, _ : isUnsignedType ?it2 |- context[isUsualArithmeticInteger ?P ?it1 ?it2 _]] =>
        set (ltIntegerRank_fun_correct P it2 it1);
        set (ltIntegerRank_fun_correct P it1 it2);
        (try destruct_integerBaseType);
        boolSpec_simpl;
        my_auto'
          ltac:(solve [ apply IsUsualArithmeticIntegerLtSameUnsigned; assumption
                      | apply IsUsualArithmeticIntegerGtSameUnsigned; assumption])
          fail
    | [_ : isSignedType   ?it1, _ : isUnsignedType ?it2 |- context[isUsualArithmeticInteger ?P ?it1 ?it2 _]] =>
        set (leIntegerRank_fun_correct P it1 it2) as Hle_correct;
        set (leIntegerRank_fun_correct P it2 it1) as Hge_correct;
        set (leIntegerTypeRange_fun_correct P it2 it1) as HleRange_correct;
        set (isCorrespondingUnsigned_fun_correct it1 it3) as Hcorr_correct;
        destruct_integerType;
        my_auto'
          ltac:(solve [ apply IsUsualArithmeticIntegerLtUnsigned; my_auto
                      | apply IsUsualArithmeticIntegerGtSigned  ; my_auto
                      | apply IsUsualArithmeticIntegerGtSigned' ; my_auto ])
          ltac:(progress boolSpec_simpl)
    | [_ : isUnsignedType ?it1, _ : isSignedType   ?it2 |- context[isUsualArithmeticInteger ?P ?it1 ?it2 ?it3]] =>
        set (leIntegerRank_fun_correct P it1 it2) as Hle_correct;
        set (leIntegerRank_fun_correct P it2 it1) as Hge_correct;
        set (leIntegerTypeRange_fun_correct P it1 it2) as HleRange_correct;
        set (isCorrespondingUnsigned_fun_correct it2 it3) as Hcorr_correct;
        destruct_integerType;
        boolSpec_simpl;
        my_auto;
        match goal with
        | [_ : context [leIntegerRank_fun _ _] |- _] =>
            (* TODO Not sure why Coq fails to simplify here. *)
            unfold leIntegerRank_fun in Hle_correct;
            unfold ltIntegerRank_fun in Hle_correct;
            unfold eqIntegerRank_fun in Hle_correct;
            unfold leIntegerRank_fun in Hge_correct;
            unfold ltIntegerRank_fun in Hge_correct;
            unfold eqIntegerRank_fun in Hge_correct
        | _ => idtac
        end;
        boolSpec_simpl;
        my_auto'
          ltac:(solve [ apply IsUsualArithmeticIntegerLtSigned  ; my_auto
                      | apply IsUsualArithmeticIntegerGtUnsigned; my_auto ])
          fail
    | _ => repeat destruct_decide; finish fail
    end).
Qed.

Lemma isUsualArithmeticInteger_find_correct P it1 it2 :
  match isUsualArithmeticInteger_find P it1 it2 with
  | Some it3 => isUsualArithmeticInteger P it1 it2 it3
  | None     => forall it3, neg (isUsualArithmeticInteger P it1 it2 it3)
  end.
Proof.
  destruct_integerType; simpl;
  match goal with
  | [|- isUsualArithmeticInteger ?P ?it1 ?it2 ?it3] =>
      exact (isUsualArithmeticInteger_fun_correct P it1 it2 it3)
  | [|- forall _, neg (isUsualArithmeticInteger ?P ?it1 ?it2 _)] =>
      intros it3;
      exact (isUsualArithmeticInteger_fun_correct P it1 it2 it3)
  | _ =>
    unfold_goal; simpl;
    match goal with
    | [|- match ?c with _ => _ end] =>
        let Heq := fresh in
        match c with
        | context[Z.ltb ?x ?y] => case_eq (Z.ltb x y); intros Heq
        end;
        match goal with
        | [|- isUsualArithmeticInteger ?P ?it1 ?it2 ?it3] =>
            let H := fresh in
            set (isUsualArithmeticInteger_fun_correct P it1 it2 it3) as H;
            unfold isUsualArithmeticInteger_fun in H;
            boolSpec_simpl;
            rewrite Heq in H;
            assumption
        end
    end
  end.
Qed.

Lemma isUsualArithmeticInteger_find_unique P it1 it2 it3 :
  isUsualArithmeticInteger P it1 it2 it3 ->
  isUsualArithmeticInteger_find P it1 it2 = Some it3.
Proof.
  set (isSignedType_fun_correct it1).
  set (isSignedType_fun_correct it2).
  set (isUnsignedType_fun_correct it1).
  set (isUnsignedType_fun_correct it2).
  set (ltIntegerRank_fun_correct P it1 it2).
  set (ltIntegerRank_fun_correct P it2 it1).
  set (leIntegerRank_fun_correct P it1 it2).
  set (leIntegerRank_fun_correct P it2 it1).
  set (leIntegerTypeRange_fun_correct P it2 it1).
  set (leIntegerTypeRange_fun_correct P it1 it2).
  inversion 1;
  unfold isUsualArithmeticInteger_find;
  my_auto;
  repeat match goal with
  | [it : integerType|- _] => destruct it
  end;
  my_auto;
  abstract (destruct_integerType; boolSpec_simpl; my_auto).
Qed.

Definition isUsualArithmetic_find_correct P t1 t2 :
  match isUsualArithmetic_find P t1 t2 with
  | Some t3 => isUsualArithmetic P t1 t2 t3
  | None    => forall t3, neg (isUsualArithmetic P t1 t2 t3)
  end.
Proof.
  unfold_goal.
  destruct t1; destruct t2;
  repeat match goal with
  | [bt : basicType|- _] => destruct bt
  end;
  match goal with
  | [|- forall _, neg _] => inversion 1
  | [|- context[isUsualArithmeticInteger_find P
                  (isIntegerPromotion_find P ?it1)
                  (isIntegerPromotion_find P ?it2)]] =>
      let Heq1 := fresh in
      let Heq2 := fresh in
      let Heq3 := fresh in
      set (isIntegerPromotion_find_correct P it1);
      set (isIntegerPromotion_find_correct P it2);
      set (isUsualArithmeticInteger_find_correct P (isIntegerPromotion_find P it1) (isIntegerPromotion_find P it2));
      case_eq (isIntegerPromotion_find P it1);
      match goal with
      | [|- forall (_ : integerBaseType), _ -> _] => intros ? Heq1
      | _ => intros Heq1
      end;
      case_eq (isIntegerPromotion_find P it2);
      match goal with
      | [|- forall (_ : integerBaseType), _ -> _] => intros ? Heq2
      | _ => intros Heq2
      end;
      case_eq (isUsualArithmeticInteger_find P (isIntegerPromotion_find P it1) (isIntegerPromotion_find P it2));
      match goal with
      | [|- forall (_ : integerType), _ = Some _ -> _] => intros ? Heq3
      | [|- _ = None                             -> _] => intros Heq3
      | _ => idtac
      end;
      rewrite Heq1 in *;
      rewrite Heq2 in *;
      rewrite Heq3 in *;
      (try rewrite <- Heq1);
      (try rewrite <- Heq2);
      (try rewrite    Heq3);
      simpl;
      solve [ econstructor; eassumption
            | inversion 1; my_auto; intuition
            | destruct t3; inversion 1; my_auto;
              match goal with
              | [ H1 : isIntegerPromotion ?P ?it1 ?it1'
              , H2 : isIntegerPromotion ?P ?it2 ?it2'
              , _  : isUsualArithmeticInteger _ _ _ ?it3
              , H  : forall _, neg (isUsualArithmeticInteger _ _ _ _) |- _] =>
                set (isIntegerPromotion_find_unique P it1 it1' H1);
                set (isIntegerPromotion_find_unique P it2 it2' H2);
                apply (H it3); congruence
              end
            ]
  end.
Qed.

Definition isUsualArithmetic_find_unique {P} {t1 t2 t3} :
  isUsualArithmetic P t1 t2 t3 ->
  isUsualArithmetic_find P t1 t2 = Some t3.
Proof.
  inversion 1; subst.
  unfold isUsualArithmetic_find.
  match goal with
  | [ H1 : isIntegerPromotion ?P ?it1 ?it1'
    , H2 : isIntegerPromotion ?P ?it2 ?it2'
    , H3 : isUsualArithmeticInteger ?P ?it1' ?it2' ?it3 |- _] =>
      let Heq1 := fresh in
      let Heq2 := fresh in
      let Heq3 := fresh in
      set (isIntegerPromotion_find_unique P it1 it1' H1) as Heq1;
      rewrite Heq1;
      set (isIntegerPromotion_find_unique P it2 it2' H2) as Heq2;
      rewrite Heq2;
      set (isUsualArithmeticInteger_find_unique P it1' it2' it3 H3) as Heq3;
      rewrite Heq3
  end.
  congruence.
Qed.

Lemma isUsualArithmetic_Integer P it1 it2 :
  {t : type & isUsualArithmetic P (Basic (Integer it1)) (Basic (Integer it2)) t}.
Proof.
  set (isIntegerPromotion_find_correct P it1) as H1.
  set (isIntegerPromotion_find_correct P it2) as H2.
  set (isIntegerPromotion_find P it1) as pit1 in *.
  set (isIntegerPromotion_find P it2) as pit2 in *.
  set (isUsualArithmeticInteger_find_correct P pit1 pit2) as Husual.
  unfold isUsualArithmeticInteger_find in Husual.
  case_eq pit1; first [intros ibt1 Heq1 | intros Heq1];
  case_eq pit2; first [intros ibt2 Heq2 | intros Heq2];
  rewrite Heq1 in *; rewrite Heq2 in *;
  destruct (isIntegerPromotion_Signed_Unsigned H1);
  destruct (isIntegerPromotion_Signed_Unsigned H2);
  match goal with
  | [H : isSignedType   _ |- _] => now inversion H
  | [H : isUnsignedType _ |- _] => now inversion H
  | [H : isIntegerPromotion P ?it1 Bool |- _] => 
      inversion H; exfalso; unfold not in *; apply_ctx;
      set (ltIntegerRank_fun_correct P Bool (Signed Int));
      constructor 2; assumption
  | _ =>
      match type of Husual with
      | context [if ?d then _ else _] =>
          let Heq := fresh in
          case_eq d; intros Heq; rewrite Heq in Husual; simpl in Husual;
          revert Husual; context_destruct_all;
          eexists; econstructor (eassumption)
      end
  end.
Qed.

Lemma isUsualArithmetic_find_Integer_Some {P} {it1 it2} :
  {t : type & isUsualArithmetic_find P (Basic (Integer it1)) (Basic (Integer it2)) = Some t}.
Proof.
  destruct (isUsualArithmetic_Integer P it1 it2) as [t H].
  exists t.
  exact (isUsualArithmetic_find_unique H).
Qed.

Lemma isUsualArithmetic_find_Integer_None {P} {it1 it2} :
  neg (isUsualArithmetic_find P (Basic (Integer it1)) (Basic (Integer it2)) = None).
Proof.
  destruct (isUsualArithmetic_Integer P it1 it2) as [t H].
  set (isUsualArithmetic_find_unique H).
  intros ?; congruence.
Qed.

Lemma isUsualArithmetic_fun_correct P t1 t2 t3 :
  boolSpec (isUsualArithmetic_fun P t1 t2 t3) (isUsualArithmetic P t1 t2 t3).
Proof.
  do 2 unfold_goal.
  set (isUsualArithmetic_find_correct P t1 t2) as Hcorrect.
  set (@isUsualArithmetic_find_unique P t1 t2 t3) as Hunique.
  my_auto.
  + match goal with | [Heq : _ = Some _|- _] => rewrite Heq in Hcorrect; assumption end.
  + intros Husual; set (Hunique Husual); contradiction.
Qed.

Lemma isObject_fun_correct t : boolSpec (isObject_fun t) (isObject t).
Proof. destruct t; my_auto. Qed.

Lemma isComplete_fun_correct t : boolSpec (isComplete_fun t) (isComplete t).
Proof. destruct t; my_auto. Qed.

Lemma isIncomplete_fun_correct t : boolSpec (isIncomplete_fun t) (isIncomplete t).
Proof. destruct t; my_auto. Qed.

Lemma isModifiable_fun_correct qs t : boolSpec (isModifiable_fun qs t) (isModifiable qs t).
Proof.
  do 2 unfold_goal.
  set (isObject_fun_correct t).
  set (isArray_fun_correct t).
  set (isIncomplete_fun_correct t).
  set (Decision_boolSpec (decide (isConstQualified qs) true : Decision (_ = _))).
  my_auto' fail ltac:(progress (bool_simpl; boolSpec_simpl)).
Qed.

Lemma isReal_fun_correct t : boolSpec (isReal_fun t) (isReal t).
Proof.
  do 2 unfold_goal.
  generalize (isInteger_fun_correct t).
  destruct (isInteger_fun t);
  my_auto.
Qed.

Lemma isLvalueConvertible_fun_correct t : boolSpec (isLvalueConvertible_fun t) (isLvalueConvertible t).
Proof.
  do 2 unfold_goal.
  set (isArray_fun_correct t).
  set (isComplete_fun_correct t).
  my_auto' fail ltac:(progress (bool_simpl; boolSpec_simpl)).
Qed.

Fixpoint isCompatible_fun_correct        t1 t2 : boolSpec (isCompatible_fun        t1 t2) (isCompatible       t1 t2)
with     isCompatible_params_fun_correct p1 p2 : boolSpec (isCompatible_params_fun p1 p2) (isCompatible_params p1 p2).
Proof.
  + unfold_goal; destruct t1, t2; simpl; unfold andb;
    repeat match goal with
    | [|- bool_of_decision ?e = ?o -> _] => destruct e; simpl; intros ?; subst o; subst
    | [|- isCompatible_fun ?t1 ?t2 = ?o -> _] => case_fun (isCompatible_fun_correct t1 t2)
    | [|- isCompatible_params_fun ?t1 ?t2 = ?o -> _] => case_fun (isCompatible_params_fun_correct t1 t2)
    | _ => context_destruct
    end; boolSpec_simpl; finish fail.
  + unfold_goal.
    destruct p1; destruct p2; simpl; unfold andb;
    repeat match goal with
    | [|- isCompatible_fun ?t1 ?t2 = ?o -> _] => case_fun (isCompatible_fun_correct t1 t2)
    | [|- isCompatible_params_fun ?t1 ?t2 = ?o -> _] => case_fun (isCompatible_params_fun_correct t1 t2)
    | _ => context_destruct
    end; boolSpec_simpl; finish fail.
Defined.

Fixpoint isComposite_fun_correct        t1 t2 t3 : boolSpec (isComposite_fun        t1 t2 t3) (isComposite        t1 t2 t3)
with     isComposite_params_fun_correct p1 p2 p3 : boolSpec (isComposite_params_fun p1 p2 p3) (isComposite_params p1 p2 p3).
Proof.
  + unfold_goal.
    destruct t1, t2, t3; simpl;
    unfold andb;
    repeat match goal with
    | [|- bool_of_decision ?e = ?o                -> _] => destruct e; simpl; intros ?; subst o; subst
    | [|- isComposite_fun        ?t1 ?t2 ?t3 = ?o -> _] => case_fun (isComposite_fun_correct t1 t2 t3)
    | [|- isComposite_params_fun ?p1 ?p2 ?p3 = ?o -> _] => case_fun (isComposite_params_fun_correct p1 p2 p3)
    | _ => context_destruct
    end; boolSpec_simpl; finish fail.
  + unfold_goal.
    destruct p1, p2, p3; simpl;
    unfold andb;
    repeat match goal with
    | [|- isUnqualified_fun ?qs = ?o              -> _] => case_fun (isUnqualified_fun_correct qs)
    | [|- isComposite_fun        ?t1 ?t2 ?t3 = ?o -> _] => case_fun (isComposite_fun_correct t1 t2 t3)
    | [|- isComposite_params_fun ?p1 ?p2 ?p3 = ?o -> _] => is_var o; case_fun (isComposite_params_fun_correct p1 p2 p3)
    | _ => context_destruct
    end; boolSpec_simpl; finish fail.
Qed.

Fixpoint isComposite_find_correct t1 t2 :
  optionSpec (isComposite_find t1 t2) (isComposite t1 t2)
with isComposite_params_find_correct p1 p2 :
  optionSpec (isComposite_params_find p1 p2) (isComposite_params p1 p2).
Proof.
  + unfold_goal.
    destruct t1, t2; simpl;
    unfold option_map;
    repeat match goal with
    | [|- bool_of_decision ?e = ?o -> _] => is_var o; destruct e; subst; intros ?; subst o; simpl
    | [|- isComposite_find        ?t1 ?t2 = ?o -> _] => case_fun (isComposite_find_correct t1 t2); unfold optionSpec in *
    | [|- isComposite_params_find ?p1 ?p2 = ?o -> _] => case_fun (isComposite_params_find_correct p1 p2); unfold optionSpec in *
    | [|- isComposite _ _ _] => econstructor (solve [eassumption|reflexivity])
    | [|- forall _, neg (isComposite _ _ _)] => inversion 1; subst
    | _ => context_destruct
    end; solve [congruence | firstorder].
  + unfold_goal.
    destruct p1, p2; simpl.
    - constructor.
    - inversion 1.
    - inversion 1.
    - repeat match goal with
      | [|- isComposite_find ?t1 ?t2 = ?o -> _] => is_var o; case_fun (isComposite_find_correct t1 t2); unfold optionSpec in *
      | [|- isComposite_params_find ?p1 ?p2 = ?o -> _] => is_var o; case_fun (isComposite_params_find_correct p1 p2); unfold optionSpec in *
      | [|- isComposite_params _ _ _] => econstructor (solve [eassumption|reflexivity])
      | [|- forall _, neg (isComposite_params _ _ _)] => inversion 1; subst
      | _ => context_destruct
      end; firstorder.
Qed.

Fixpoint isComposite_find_unique t1 t2 :
  optionUnique (isComposite_find t1 t2) (isComposite t1 t2)
with isComposite_params_find_unique p1 p2 :
  optionUnique (isComposite_params_find p1 p2) (isComposite_params p1 p2).
Proof.
  + unfold_goal.
    intros ? H.
    destruct t1, t2; simpl;
    unfold option_map;
    inversion H; subst;
    repeat match goal with
    | [|- bool_of_decision ?e = ?o -> _] => is_var o; destruct e; subst; intros ?; subst o; simpl
    | [|- isComposite_find        ?t1 ?t2 = ?o -> _] => case_fun (isComposite_find_unique t1 t2); unfold optionUnique in *
    | [|- isComposite_params_find ?p1 ?p2 = ?o -> _] => case_fun (isComposite_params_find_unique p1 p2); unfold optionUnique in *
    | _ => context_destruct
    | [Heq : forall _, isComposite ?ty1 ?ty2 _ -> Some ?t = Some _ , H : isComposite ?ty1 ?ty2 ?ty3 |- _] => notSame t ty3; injection (Heq _ H); intros; subst
    | [Heq : forall _, isComposite ?ty1 ?ty2 _ -> None = Some _ , H : isComposite ?ty1 ?ty2 _ |- _] => discriminate (Heq _ H)
    | [Heq : forall _, isComposite_params ?p1 ?p2 _ -> Some ?p = Some _ , H : isComposite_params ?p1 ?p2 ?p' |- _] => notSame p p'; injection (Heq _ H); intros; subst
    | [Heq : forall _, isComposite_params ?p1 ?p2 _ -> None = Some _ , H : isComposite_params ?p1 ?p2 _ |- _] => discriminate (Heq _ H)
    end; congruence.
  + unfold_goal.
    destruct p1, p2; simpl;
    inversion 1; subst.
    - reflexivity.
    - repeat match goal with
      | [|- bool_of_decision ?e = ?o -> _] => is_var o; destruct e; subst; intros ?; subst o; simpl
      | [|- isComposite_find        ?t1 ?t2 = ?o -> _] => case_fun (isComposite_find_unique t1 t2); unfold optionUnique in *
      | [|- isComposite_params_find ?p1 ?p2 = ?o -> _] => case_fun (isComposite_params_find_unique p1 p2); unfold optionUnique in *
      | _ => context_destruct
      | [Heq : forall _, isComposite ?ty1 ?ty2 _ -> Some ?t = Some _ , H : isComposite ?ty1 ?ty2 ?ty3 |- _] => notSame t ty3; injection (Heq _ H); intros; subst
      | [Heq : forall _, isComposite ?ty1 ?ty2 _ -> None = Some _ , H : isComposite ?ty1 ?ty2 _ |- _] => discriminate (Heq _ H)
      | [Heq : forall _, isComposite_params ?p1 ?p2 _ -> Some ?p = Some _ , H : isComposite_params ?p1 ?p2 ?p' |- _] => notSame p p'; injection (Heq _ H); intros; subst
      | [Heq : forall _, isComposite_params ?p1 ?p2 _ -> None = Some _ , H : isComposite_params ?p1 ?p2 _ |- _] => discriminate (Heq _ H)
      | [H : isUnqualified ?qs |- _] => inversion_clear H
      end; congruence.
Qed.
