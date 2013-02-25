Require Import List.

Require Import AilSyntax Implementation.

(** funs TypeTransformation *)
Fixpoint addQualifiers qs t : type :=
  match t with
  | Void    qs'     => Void    (QualifierSet.union qs qs')
  | Basic   qs' bt' => Basic   (QualifierSet.union qs qs') bt'
  | Pointer qs' t'  => Pointer (QualifierSet.union qs qs') t'
  | _ => t
end.

Fixpoint QualifiersOf t : qualifiers:=
  match t with
  | Void    qs   => qs
  | Basic   qs _ => qs
  | Pointer qs _ => qs
  | _            => QualifierSet.empty
  end.

Definition MergeQualifiers t1 t2 :=
  QualifierSet.union (QualifiersOf t1) (QualifiersOf t2).

Fixpoint Unqualify t : type :=
  match t with
  | Void    _     => Void    QualifierSet.empty
  | Basic   _ bt' => Basic   QualifierSet.empty bt'
  | Pointer _ t'  => Pointer QualifierSet.empty t'
  | _ => t
end.

Fixpoint PointerConvert t : type :=
  match t with
  |  Array t' n'         => Pointer QualifierSet.empty t'
  |  Function t' t_list' => Pointer QualifierSet.empty (Function t' t_list')
  | _ => t
  end.

Definition qualifiersSub t1 t2 : Prop := QualifierSet.subset (QualifiersOf t1) (QualifiersOf t2) = true.

(*with isRegister : type -> Prop :=    (* defn isRegister *)*)
Definition isConst t : Prop := QualifierSet.mem Const (QualifiersOf t) = true.

Inductive isSigned : P -> type -> Prop :=    (* defn isSigned *)
 | IsSignedInt : forall P qs it, isSigned P (Basic qs (Integer (Signed it))) 
 | IsSignedChar : forall P qs, isCharSigned P = true -> isSigned P (Basic qs Char).

Inductive isUnsigned : P -> type -> Prop :=    (* defn isUnsigned *)
 | IsUnsignedInt : forall P qs ibt,
     isUnsigned P (Basic qs (Integer (Unsigned ibt))) 
 | IsUnsignedBool : forall P qs,
     isUnsigned P (Basic qs (Integer Bool)) 
 | IsUnsignedChar : forall P qs,
      ~ (isCharSigned P = true)  ->
     isUnsigned P (Basic qs Char).

Inductive isInteger :=    (* defn isInteger *)
 | IsIntegerInteger : forall qs it,
     isInteger  (Basic qs (Integer it)) 
 | IsIntegerChar : forall qs,
     isInteger  (Basic qs Char).

Inductive eqRank : type -> type -> Prop :=    (* defn eqRank *)
 | EqRankUnsigned : forall ibt,
     eqRank (Basic QualifierSet.empty (Integer (Signed ibt))) (Basic QualifierSet.empty (Integer (Unsigned ibt)))
 | EqRankUnsignedChar : 
     eqRank (Basic QualifierSet.empty Char) (Basic QualifierSet.empty (Integer (Unsigned IChar)))
 | EqRankSignedChar : 
     eqRank (Basic QualifierSet.empty Char) (Basic QualifierSet.empty (Integer (Signed IChar)))
 | EqRankSym : forall ty1 ty2,
     eqRank ty1 ty2 -> eqRank ty2 ty1
 | EqRankEq : forall ty,
     isInteger ty -> eqRank ty ty.

Inductive isBool : type -> Prop :=    (* defn isBool *)
 | IsBoolDef : forall qs,
     isBool (Basic qs (Integer Bool)).

Inductive ltRank : P -> type -> type -> Prop :=    (* defn ltRank *)
 | LtRankPrecision : forall P ty1 ty2,
      (precision P)  ty1  <  precision P ty2  ->
     ltRank P ty1 ty2
 | LtRankBool : forall P ty,
     isInteger ty ->
     not (isBool ty) ->
     ltRank P (Basic QualifierSet.empty (Integer Bool)) ty
 | LtRankLongLong : forall P,
     ltRank P (Basic QualifierSet.empty (Integer (Signed Long))) (Basic QualifierSet.empty (Integer (Signed LongLong)))
 | LtRankLong : forall P,
     ltRank P (Basic QualifierSet.empty (Integer (Signed Int))) (Basic QualifierSet.empty (Integer (Signed Long)))
 | LtRankInt : forall P,
     ltRank P (Basic QualifierSet.empty (Integer (Signed Short))) (Basic QualifierSet.empty (Integer (Signed Int)))
 | LtRankShort : forall P,
     ltRank P (Basic QualifierSet.empty (Integer (Signed IChar))) (Basic QualifierSet.empty (Integer (Signed Short)))
 | LtRankTransitive : forall P ty1 ty2 ty,
     ltRank P ty1 ty ->
     ltRank P ty ty2 ->
     ltRank P ty1 ty2
 | LtRankCongruence : forall P ty1 ty2 ty1' ty2',
     eqRank ty1 ty1' ->
     eqRank ty2 ty2' ->
     ltRank P ty1' ty2' ->
     ltRank P ty1 ty2.

Inductive leRank : P -> type -> type -> Prop :=    (* defn leRank *)
 | LeRankEq : forall P ty1 ty2,
     eqRank ty1 ty2 ->
     leRank P ty1 ty2
 | LeRankLt : forall P ty1 ty2,
     ltRank P ty1 ty2 ->
     leRank P ty1 ty2.

Inductive isVoid : type -> Prop :=    (* defn isVoid *)
 | IsVoidDef : forall q, isVoid  (Void q). 

Inductive isPointer : type -> Prop :=    (* defn isPointer *)
 | IsPointerDef : forall qs ty,
     isPointer (Pointer qs ty).

Inductive isArithmetic : type -> Prop :=    (* defn isArithmetic *)
 | IsArithmeticInteger : forall ty, isInteger ty -> isArithmetic ty.

Inductive isScalar : type -> Prop :=    (* defn isScalar *)
 | IsScalarPointer : forall t, isPointer t -> isScalar t
 | IsScalarArithmetic : forall t, isArithmetic t -> isScalar t.

Inductive isArray : type -> Prop :=    (* defn isArray *)
 | IsArrayDef : forall t n, isArray (Array t n).

Inductive isFunction : type -> Prop :=    (* defn isFunction *)
 | IsFunctionDef : forall t_list t, isFunction  (Function t t_list).

(* TODO signedness of char is dependent on P! *)
Inductive isCorrespondingUnsigned : type -> type -> Prop :=    (* defn isCorrespondingUnsigned *)
 | IsCorrespondingUnsignedDef : forall ibt,
     isCorrespondingUnsigned
       (Basic QualifierSet.empty (Integer (Signed   ibt)))
       (Basic QualifierSet.empty (Integer (Unsigned ibt))).

Inductive isPromotion : P -> type -> type -> Prop :=    (* defn isPromotion *)
 | IsPromotionToSignedInt : forall P it,
      ~ it = Unsigned Int ->
      ~ it = Signed Int   ->
     leRank  P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Signed Int))) ->
     leRange P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Signed Int))) ->
     isPromotion P (Basic QualifierSet.empty (Integer it))  (Basic QualifierSet.empty (Integer (Signed Int))) 
 | IsPromotionToUnsignedInt : forall P it,
      ~ it = Unsigned Int ->
      ~ it = Signed Int   ->
     leRank P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Signed Int))) ->
      ~ leRange  P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Signed   Int)))  ->
     isPromotion P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Unsigned Int))) 
 | IsPromotionUnsignedInt : forall P,
     isPromotion P
       (Basic QualifierSet.empty (Integer (Unsigned Int)))
       (Basic QualifierSet.empty (Integer (Unsigned Int)))
 | IsPromotionSignedInt : forall P,
     isPromotion P
       (Basic QualifierSet.empty (Integer (Signed Int)))
       (Basic QualifierSet.empty (Integer (Signed Int)))
 | IsPromotionRank : forall P it,
      ~ leRank   P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer (Signed Int))) ->
     isPromotion P (Basic QualifierSet.empty (Integer it)) (Basic QualifierSet.empty (Integer  it         )).

Inductive isComplete : type -> Prop :=
 | IsCompleteBasicType : forall qs bt, isComplete (Basic qs bt) 
 | IsCompletePointer   : forall qs t,  isComplete (Pointer qs t) 
 | IsCompleteArray     : forall ty n,  isComplete (Array ty n).

Inductive isIncomplete : type -> Prop :=
 | IsIncompleteVoid : forall qs, isIncomplete (Void qs).

Inductive isUsualArithmetic : P -> type -> type -> type -> Prop :=
 | IsUsualArithmeticEq : forall P ty1 ty2 ty,
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty ->
     isPromotion P ty2 ty ->
     isUsualArithmetic P ty1 ty2 ty
 | IsUsualArithmeticGtSameSigned : forall P ty1 ty2 ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' = ty2' ->
     isSigned P ty1' ->
     isSigned P ty2' ->
     ltRank P ty2' ty1' ->
     isUsualArithmetic P ty1 ty2 ty1'
 | IsUsualArithmeticGtSameUnsigned : forall P ty1 ty2 ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' = ty2' ->
     isUnsigned P ty1' ->
     isUnsigned P ty2' ->
     ltRank P ty2' ty1' ->
     isUsualArithmetic P ty1 ty2 ty1'
 | IsUsualArithmeticLtSameSigned : forall P ty1 ty2 ty2' ty1',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' =  ty2' ->
     isSigned P ty1' ->
     isSigned P ty2' ->
     ltRank P ty1' ty2' ->
     isUsualArithmetic P ty1 ty2 ty2'
 | IsUsualArithmeticLtSameUnsigned : forall P ty1 ty2 ty2' ty1',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' =  ty2' ->
     isUnsigned P ty1' ->
     isUnsigned P ty2' ->
     ltRank P ty1' ty2' ->
     isUsualArithmetic P ty1 ty2 ty2'
 | IsUsualArithmeticLtUnsigned : forall P ty1 ty2 ty2' ty1',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' = ty2' ->
     isSigned P ty1' ->
     isUnsigned P ty2' ->
     leRank P ty1' ty2' ->
     isUsualArithmetic P ty1 ty2 ty2'
 | IsUsualArithmeticGtUnsigned : forall P ty1 ty2 ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1'  = ty2' ->
     isUnsigned P ty1' ->
     isSigned P ty2' ->
     leRank P ty2' ty1' ->
     isUsualArithmetic P ty1 ty2 ty1'
 | IsUsualArithmeticLtSigned : forall P ty1 ty2 ty2' ty1',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1'  =  ty2' ->
     isUnsigned P ty1' ->
     isSigned P ty2' ->
     leRank P ty1' ty2' ->
     leRange P ty1' ty2' ->
     isUsualArithmetic P ty1 ty2 ty2'
 | IsUsualArithmeticGtSigned : forall P ty1 ty2 ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' = ty2' ->
     isSigned P ty1' ->
     isUnsigned P ty2' ->
     leRank P ty2' ty1' ->
     leRange P ty2' ty1' ->
     isUsualArithmetic P ty1 ty2 ty1'
 | IsUsualArithmeticLtSigned' : forall P ty1 ty2 ty2'' ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1' =  ty2' ->
     isUnsigned P ty1' ->
     isSigned P ty2' ->
     leRank P ty1' ty2' ->
      ~ leRange P ty1' ty2' ->
     isCorrespondingUnsigned ty2' ty2'' ->
     isUsualArithmetic P ty1 ty2 ty2''
 | IsUsualArithmeticGtSigned' : forall P ty1 ty2 ty1'' ty1' ty2',
     isInteger ty1 ->
     isInteger ty2 ->
     isPromotion P ty1 ty1' ->
     isPromotion P ty2 ty2' ->
      ~ ty1'  =  ty2' ->
     isSigned P ty1' ->
     isUnsigned P ty2' ->
     leRank P ty2' ty1' ->
      ~ leRange P ty2' ty1' ->
     isCorrespondingUnsigned ty1' ty1'' ->
     isUsualArithmetic P ty1 ty2 ty1''.

Inductive isLvalueConversion : type -> type -> Prop :=    (* defn isLvalueConversion *)
 | IsLvalueConversionDef : forall ty,
      ~ isArray ty ->
     isComplete ty ->
     isLvalueConversion ty (Unqualify ty).

Inductive isObject : type -> Prop :=    (* defn isObject *)
 | IsObjectBasicType : forall qs bt, isObject (Basic qs bt)
 | IsObjectVoid      : forall qs,    isObject (Void qs) 
 | IsObjectPointer   : forall qs ty, isObject (Pointer qs ty) 
 | IsObjectArray     : forall ty n,  isObject (Array ty n).

Inductive isModifiable : type -> Prop :=    (* defn isModifiable *)
 | IsModifiableDef : forall ty,
      ~ isArray ty ->
      ~ isIncomplete ty->
      ~ isConst ty ->
     isModifiable ty.

Inductive isReal : type -> Prop :=    (* defn isReal *)
 | IsRealInteger : forall ty, isInteger ty-> isReal ty.

Inductive isCompatible : type -> type -> Prop :=    (* defn isCompatible *)
 | IsCompatibleEq : forall ty, isCompatible ty ty.

Inductive isComposite : type -> type -> type -> Prop :=    (* defn isComposite *)
 | IsCompositeEq : forall ty, isComposite ty ty ty
 | IsCompositeArray : forall ty1 ty2 ty n,
     isComposite ty1 ty2 ty ->
     isComposite (Array ty1 n) (Array ty2 n) (Array ty n) 
 | IsCompositeFunction : forall ty1_result ty2_result ty_result ty1_list ty2_list ty_list n,
     length ty1_list = n ->
     length ty2_list = n ->
     length ty_list  = n ->
     isComposite ty1_result ty2_result ty_result ->
     (forall ty1 ty2 ty, In ((ty1, ty2), ty) (combine (combine ty1_list ty2_list) ty_list) -> isComposite ty1 ty2 ty) ->
     isComposite (Function ty1_result ty1_list) (Function ty2_result ty2_list) (Function ty_result ty_list).

Lemma isPromotion_inj P ty : forall ty1 ty2,
  isPromotion P ty ty1 -> isPromotion P ty ty2 -> ty1 = ty2.
Proof.
  induction ty;
  intros ty1 ty2 P1 P2;
  inversion P1; subst;
  inversion P2; subst;
  auto;
  try contradiction.
    now (destruct H1).
    now (destruct H2).
    now (destruct H0).
    now (destruct H1).
Qed.

Lemma isLvalueConversion_inj ty : forall ty1 ty2,
  isLvalueConversion ty ty1 -> isLvalueConversion ty ty2 -> ty1 = ty2.
Proof.
  induction ty;
  intros ty1 ty2 L1 L2;
  
  inversion L1; subst;
  inversion L2; subst;
  congruence.
Qed.

Ltac isInteger_False :=
  match goal with
  | [ H : isInteger (Void _)       |- _] => inversion H
  | [ H : isInteger (Array _ _)    |- _] => inversion H
  | [ H : isInteger (Function _ _) |- _] => inversion H
  | [ H : isInteger (Pointer _ _)  |- _] => inversion H
  end.

Ltac isSigned_False :=
  match goal with
  | [ H : isSigned _ (Void _)               |- _] => inversion H
  | [ H : isSigned _ (Array _ _)            |- _] => inversion H
  | [ H : isSigned _ (Function _ _)         |- _] => inversion H
  | [ H : isSigned _ (Pointer _ _)          |- _] => inversion H
  | [ H : isSigned _ (Basic _ (Integer Bool)) |- _] => inversion H
  | [ H : isSigned _ (Basic _ (Integer (Unsigned _))) |- _] => inversion H
  end.

Ltac isUnsigned_False :=
  match goal with
  | [ H : isUnsigned _ (Void _)               |- _] => inversion H
  | [ H : isUnsigned _ (Array _ _)            |- _] => inversion H
  | [ H : isUnsigned _ (Function _ _)         |- _] => inversion H
  | [ H : isUnsigned _ (Pointer _ _)          |- _] => inversion H
  | [ H : isUnsigned _ (Basic _ (Integer Bool)) |- _] => inversion H
  | [ H : isUnsigned _ (Basic _ (Integer (Unsigned _))) |- _] => inversion H
  end.

Ltac isCorrespondingUnsigned_False :=
  match goal with
  | [ H : isCorrespondingUnsigned _ (Basic _ (Integer (Signed _))) |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned _ (Basic _ (Integer Bool)) |- _] =>
      inversion H
(*
  | [ H : isCorrespondingUnsigned _ (Basic _ Char) |- _] =>
      inversion H
*)
  | [ H : isCorrespondingUnsigned _ (Void _) |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned _ (Array _ _) |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned _ (Function _ _) |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned _ (Pointer _ _) |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned (Basic _ (Integer (Unsigned _))) _ |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned (Basic _ (Integer Bool)) _ |- _] =>
      inversion H
(*
  | [ H : isCorrespondingUnsigned (Basic _ Char) _ |- _] =>
      inversion H
*)
  | [ H : isCorrespondingUnsigned (Void _) _ |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned (Array _ _) _ |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned (Function _ _) _ |- _] =>
      inversion H
  | [ H : isCorrespondingUnsigned (Pointer _ _) _ |- _] =>
      inversion H
  end.

Ltac isPromotion_simp :=
  match goal with
  | [ H1 : isPromotion ?P ?ty _
    , H2 : isPromotion ?P ?ty _ |- _] =>
      injection (isPromotion_inj P ty _ _ H1 H2) as ?; subst
  end.

Ltac isPromotion_False :=
  match goal with
  | [ H : isPromotion _ _ (Void _)               |- _] => inversion H
  | [ H : isPromotion _ _ (Array _ _)            |- _] => inversion H
  | [ H : isPromotion _ _ (Function _ _)         |- _] => inversion H
  | [ H : isPromotion _ _ (Pointer _ _)          |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ Char)         |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ (Integer Bool)) |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ (Integer (Unsigned IChar))) |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ (Integer (Unsigned Short))) |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ (Integer (Signed IChar))) |- _] => inversion H
  | [ H : isPromotion _ _ (Basic _ (Integer (Signed Short))) |- _] => inversion H
  end.

Ltac isPromotion_simp_ty ty :=
  match goal with
  | [ H1 : isPromotion ?P ty _
    , H2 : isPromotion ?P ty _ |- _] =>
      injection (isPromotion_inj P ty _ _ H1 H2) as ?; subst
  end.

Ltac isObject_function :=
  match goal with
      [H : isObject (Function _ _) |- _] => inversion H
  end.

Require Import Coq.Program.Equality.


Lemma ltRank_asymmetric_aux P t1 t2 :
  ~ ltRank P t1 t1 ->
  ltRank P t1 t2 ->
  ltRank P t2 t1 ->
  False.
Proof.
  intros Hsym H12 H21.
  set (LtRankTransitive _ _ _ _ H12 H21) as H.
  apply Hsym in H.
  exact H.
Qed.

Instance ltRank_irreflexive P : Irreflexive (ltRank P).
  unfold Irreflexive.
  unfold Reflexive.
  unfold complement.
  induction x.
  intros Lt.
  dependent induction Lt.
    omega.
    apply H0; now constructor.
    revert ty1 Lt1 Lt2.
    induction ty.
    intros
  dependent induction ltRank.
Admitted.

Lemma ltRank_asymmetric_aux P t1 t2 :
  ltRank P t1 t2 ->
  ltRank P t2 t1 ->
  False.
Proof.
  intros H1 H2.
  set (LtRankTransitive _ _ _ _ H1 H2) as H.
  apply ltRank_irreflexive in H.
  contradict H.
Qed.

Ltac ltRank_False :=
  match goal with
  | [ H1 : ltRank ?P ?t1 ?t2, H2 : ltRank ?P ?t2 ?t1 |- _] =>
      destruct (ltRank_asymmetric P t1 t2 H1 H2)
  end.

Lemma isUsualArithmetic_inj P : forall ty1 ty2 ty ty',
  isUsualArithmetic P ty ty' ty1 ->
  isUsualArithmetic P ty ty' ty2 ->
  ty1 = ty2.
Proof.
  induction ty1;
  induction ty2;
  intros ty ty' Ua1 Ua2;
  inversion Ua1; subst;
  try isPromotion_simp_ty ty;
  try isPromotion_simp_ty ty';
  try isInteger_False;
  try isSigned_False;
  try isUnsigned_False;
  try isCorrespondingUnsigned_False;
  try isPromotion_False;
  try congruence;
  inversion Ua2; subst;
  try isPromotion_simp_ty ty;
  try isPromotion_simp_ty ty';
  try isInteger_False;
  try isSigned_False;
  try isUnsigned_False;
  try isCorrespondingUnsigned_False;
  try isPromotion_False;
  try congruence;
  destruct ty; subst;
  destruct ty'; subst;
  try isPromotion_simp_ty ty;
  try isPromotion_simp_ty ty';
  try isInteger_False;
  try isSigned_False;
  try isUnsigned_False;
  try isCorrespondingUnsigned_False;
  try isPromotion_False;
  try ltRank_False;
  try congruence.
  inversion H14; subst.
  inversion H15; subst;
  try congruence.
  inversion H6.
Qed.

Hint Rewrite isPromotion_inj isLvalueConversion_inj.
Hint Resolve isPromotion_inj isLvalueConversion_inj.
