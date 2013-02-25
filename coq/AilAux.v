Require Import List.

Require Import AilSyntax.

Inductive fv : nat -> expression -> Prop :=    (* defn fv *)
 | FvUnary : forall v op eL,
     fvL v eL ->
     fv v (ExpUnary op eL)
 | FvBinary1 : forall v eL1 op eL2,
     fvL v eL1 ->
     fv v (ExpBinary eL1 op eL2)
 | FvBinary2 : forall v eL1 op eL2,
     fvL v eL1 ->
     fv v (ExpBinary eL1 op eL2)
 | FvAssign1 : forall v eL1 eL2,
     fvL v eL1 ->
     fv v (ExpAssign eL1 eL2)
 | FvAssign2 : forall v eL1 eL2,
     fvL v eL1 ->
     fv v (ExpAssign eL1 eL2)
 | FvCompoundAssign1 : forall v eL1 op eL2,
     fvL v eL1 ->
     fv v (ExpCompoundAssign eL1  op eL2)
 | FvCompoundAssign2 : forall v eL1 op eL2,
     fvL v eL1 ->
     fv v (ExpCompoundAssign eL1 op  eL2)
 | FvConditional1 : forall v eL1 eL2 eL3,
     fvL v eL1 ->
     fv v (ExpConditional eL1 eL2 eL3)
 | FvConditional2 : forall v eL1 eL2 eL3,
     fvL v eL2 ->
     fv v (ExpConditional eL1 eL2 eL3)
 | FvConditional3 : forall v eL1 eL2 eL3,
     fvL v eL2 ->
     fv v (ExpConditional eL1 eL2 eL3)
 | FvCast : forall v ty eL,
     fvL v eL ->
     fv v (ExpCast ty eL)
 | FvCall : forall v eL_list eL,
     fvL v eL ->
     fv v (ExpCall eL eL_list)
 | FvCallArgument : forall v eL_list eL,
     In eL eL_list ->
     fvL v eL ->
     fv v (ExpCall eL  eL_list)
 | FvVariable : forall v,
     fv v (ExpVariable v)
with fvL : nat -> expressionL -> Prop :=
 | FvLDef : forall v a e, fv v e -> fvL v (ExpLDef a e).

Inductive isNullPointerConstant : expressionL -> Prop :=    (* defn isNullPointerConstant *)
 | IsNullPointerConstantZero : forall l,
     isNullPointerConstant (ExpLDef l (ExpConstant (ConstantInteger (IntegerConstantSuffix 0))))
 | IsNullPointerConstantPointer : forall l eL,
     isNullPointerConstant eL ->
     isNullPointerConstant (ExpLDef l (ExpCast (Pointer QualifierSet.empty (Void QualifierSet.empty)) eL)).
