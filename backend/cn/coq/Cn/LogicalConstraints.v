Require Import BaseTypes.
Require Import IndexTerms.
Require Import Sym.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.

(* Define the logical constraint type *)
Inductive logical_constraint : Type :=
  | T : IndexTerms.t -> logical_constraint
  | Forall : (Sym.t * BaseTypes.t) -> IndexTerms.t -> logical_constraint. 

Definition t := logical_constraint.

Module LogicalConstraint_as_OrderedType <: OrderedType.
  Definition t := logical_constraint.

  Definition eq := @eq t. (* TODO: check if this is the correct definition *)

  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.  
  Proof. Admitted. (* TODO *)

  Definition lt : t -> t -> Prop.
  Proof. Admitted. (* TODO *)

  Lemma eq_refl : forall x : t, eq x x.
  Proof. Admitted. (* TODO *)

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. Admitted. (* TODO *)

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. Admitted. (* TODO *)

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. Admitted. (* TODO *)

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. Admitted. (* TODO *)

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof. Admitted. (* TODO *)

  
End LogicalConstraint_as_OrderedType.

Module LCSet := FSetAVL.Make(LogicalConstraint_as_OrderedType).

