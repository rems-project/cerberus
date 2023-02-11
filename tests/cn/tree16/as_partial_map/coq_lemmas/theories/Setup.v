(* Setup of consts and lemmas for lemmas *)

Require Import ZArith Bool.
Require CN_Lemmas.Gen_Spec.
Import CN_Lemmas.Gen_Spec.Types.
Require Import List.
Import ListNotations.
Open Scope Z.
Require Lia.

Fixpoint do_mk_arc (vals : Z -> Z) (i : Z) (num : nat) :=
  match num with
  | 0%nat => Arc_End
  | S n2 => Arc_Step (vals i) (do_mk_arc vals (i + 1) n2)
  end.

Definition mk_arc (vals : Z -> Z) (i len : Z) :=
  do_mk_arc vals i (Z.to_nat (len - i)).

Definition construct (v : Z) (ts : Z -> (tree_arc -> tree_node_option))
  (xs : tree_arc) :=
  match xs with
  | Arc_End => Node v
  | Arc_Step i ys => ts i ys
  end.
