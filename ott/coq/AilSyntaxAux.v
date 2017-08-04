Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux.
Require Import AilSyntax. 

Fixpoint null_pointer_constant' {A} (e : expression' A) : bool :=
  match e with
  | Constant (ConstantInteger (0 , None)) => true
  | Cast q (Pointer q' Void) e            => null_pointer_constant e && unqualified q && unqualified q'
  | _                                     => false
  end
with null_pointer_constant {A} e : bool :=
  match e with
  | AnnotatedExpression _ e => null_pointer_constant' e
  end.

Definition fv_arguments_aux {A} (fv : identifier -> expression A -> bool) :=
  fix fv_arguments (v : identifier) a : bool :=
    match a with
    | nil    => false
    | e :: a => fv v e || fv_arguments v a
    end.

Fixpoint fv' {A} v (e : expression' A) : bool :=
  let fv_arguments := fv_arguments_aux fv in
  match e with
  | Unary _ e => fv v e
  | Binary e1 _ e2 => orb (fv v e1) (fv v e2)
  | Assign e1 e2 => orb (fv v e1) (fv v e2)
  | CompoundAssign e1 _ e2 => orb (fv v e1) (fv v e2)
  | Conditional e1 e2 e3 => orb (fv v e1) (orb (fv v e2) (fv v e3))
  | Cast _ _ e => fv v e
  | Call e ls => orb (fv v e) (fv_arguments v ls)
  | Var v' => eq_identifier v v'
  | _ => false
  end
with fv {A} v e : bool :=
  match e with
  | AnnotatedExpression _ e => fv' v e
  end.

Definition fv_arguments {A} : identifier -> list (expression A) -> bool := fv_arguments_aux fv.
