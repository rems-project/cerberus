Require Import BaseTypes.
Require Import IndexTerms.
Require Import Sym.

Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.MSets.MSetWeakList.

(* Define the logical constraint type *)
Inductive logical_constraint : Type :=
| T : IndexTerms.t -> logical_constraint
| Forall : (Sym.t * BaseTypes.t) -> IndexTerms.t -> logical_constraint.

Definition t := logical_constraint.

Module LogicalConstraint_as_MiniDecidableType <: MiniDecidableType.
  Definition t := logical_constraint.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    (* TODO: to prove this we need define a decidable equality for all involved types and their sub-types. *)
    Admitted. (* TODO *)
End LogicalConstraint_as_MiniDecidableType.

Module LogicalConstraints_as_DecidableType := Make_UDT LogicalConstraint_as_MiniDecidableType.
Module LCSet := MSetWeakList.Make LogicalConstraints_as_DecidableType.

Definition set_from_list (l : list t) : LCSet.t :=
  List.fold_left (fun s c => LCSet.add c s) l LCSet.empty.
