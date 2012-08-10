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

Inductive isInteger : type -> Prop :=    (* defn isInteger *)
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
 | EqRankEq : forall ty,
     eqRank ty ty.

Inductive ltRank : P -> type -> type -> Prop :=    (* defn ltRank *)
 | LtRankPrecision : forall P ty1 ty2,
      (precision P)  ty1  <  precision P ty2  ->
     ltRank P ty1 ty2
 | LtRankBool : forall P ty,
     isInteger ty ->
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

Inductive isBool : type -> Prop :=    (* defn isBool *)
 | IsBoolDef : forall qs,
     isBool (Basic qs (Integer Bool)).

Inductive isArithmetic : type -> Prop :=    (* defn isArithmetic *)
 | IsArithmeticInteger : forall ty, isInteger ty -> isArithmetic ty.

Inductive isScalar : type -> Prop :=    (* defn isScalar *)
 | IsScalarPointer : forall t, isPointer t -> isScalar t
 | IsScalarArithmetic : forall t, isArithmetic t -> isScalar t.

Inductive isArray : type -> Prop :=    (* defn isArray *)
 | IsArrayDef : forall t n, isArray (Array t n).

Inductive isFunction : type -> Prop :=    (* defn isFunction *)
 | IsFunctionDef : forall t_list t, isFunction  (Function t t_list).

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

Hint Rewrite isPromotion_inj isLvalueConversion_inj.
Hint Resolve isPromotion_inj isLvalueConversion_inj.
