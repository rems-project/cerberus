Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux_defns.
Require Import AilSyntax.

(* defns Jfv *)
Inductive fv' {A} : identifier -> expression' A -> Prop :=    (* defn fv *)
 | Fv'_Unary :
     forall {v} {uop} {e},
       fv v e ->
       fv' v (Unary uop e)
 | Fv'_Binary1 :
     forall {v} {e1} {bop} {e2},
       fv v e1 ->
       fv' v (Binary e1 bop e2)
 | Fv'_Binary2 :
     forall {v} {e1} {bop} {e2},
       fv v e2 ->
       fv' v (Binary e1 bop e2)
 | Fv'_Assign1 :
     forall {v} {e1 e2},
       fv v e1 ->
       fv' v (Assign e1 e2)
 | Fv'_Assign2 :
     forall {v} {e1 e2},
     fv v e2 ->
     fv' v (Assign e1 e2)
 | Fv'_CompoundAssign1 :
     forall {v} {e1} {aop} {e2},
       fv v e1 ->
       fv' v (CompoundAssign e1 aop e2)
 | Fv'_CompoundAssign2 :
     forall {v} {e1} {aop} {e2},
       fv v e2 ->
       fv' v (CompoundAssign e1 aop e2)
 | Fv'_Conditional1 :
     forall {v} {e1 e2 e3},
       fv v e1 ->
       fv' v (Conditional e1 e2 e3)
 | Fv'_Conditional2 :
     forall {v} {e1 e2 e3},
       fv v e2 ->
       fv' v (Conditional e1 e2 e3)
 | Fv'_Conditional3 :
     forall {v} {e1 e2 e3},
       fv v e3 ->
       fv' v (Conditional e1 e2 e3)
 | Fv'_Cast :
     forall {v} {q} {t} {e},
       fv v e ->
       fv' v (Cast q t e)
 | Fv'_Call :
     forall {v} {e} {es},
       fv v e ->
       fv' v (Call e es)
 | Fv'_CallArgument :
     forall {v} {e} {es},
       fvArguments v es ->
       fv' v (Call e es)
 | Fv_Variable : forall (v:identifier),
     fv' v (Var v)
with fv {A} : identifier -> expression A -> Prop :=
 | Fv_AnnotatedExpression :
     forall {v} {a} {e},
       fv' v e ->
       fv v (AnnotatedExpression a e)
with fvArguments {A} : identifier -> list (expression A) -> Prop :=
 | FvArguments_head :
     forall {v} {e} {es},
       fv v e ->
       fvArguments v (e :: es)
 | FvArguments_tail:
     forall {v} {e} {es},
       fvArguments v es ->
       fvArguments v (e :: es).
(** definitions *)

(* defns JisNullPointerConstant *)
Inductive nullPointerConstant' {A} : expression' A -> Set :=    (* defn isNullPointerConstant *)
 | NullPointerConstant'_Zero : 
     nullPointerConstant' (Constant (ConstantInteger  ( 0 , None) ))
 | NullPointerConstant'_Pointer :
     forall {q q'} {e},
       nullPointerConstant e ->
       unqualified q  ->
       unqualified q' ->
       nullPointerConstant' (Cast q (Pointer q' Void) e)
with nullPointerConstant {A} : expression A -> Set :=
 | NullPointerConstant_AnnotatedExpression :
     forall {a} {e},
       nullPointerConstant' e ->
       nullPointerConstant (AnnotatedExpression a e).
