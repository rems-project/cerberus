(* Setup of consts and lemmas for lemmas *)

Require Import ZArith Bool.
Require CN_Lemmas.Gen_Spec CN_Lemmas.CN_Lib.
Import CN_Lemmas.Gen_Spec.Types.
Require Import List.
Import ListNotations.
Open Scope Z.
Require Import Lia.

Fixpoint to_list (xs : list_of_tree) : list tree :=
  match xs with
  | Nil_of_tree => []
  | Cons_of_tree y ys => y :: to_list ys
  end.

Fixpoint of_list (xs : list tree) : list_of_tree :=
  match xs with
  | [] => Nil_of_tree
  | y :: ys => Cons_of_tree y (of_list ys)
  end.

Lemma to_list_of_list:
  forall xs, to_list (of_list xs) = xs.
Proof.
  intro.
  induction xs.
  + auto.
  + simpl.
    rewrite IHxs.
    auto.
Qed.

Fixpoint get_array_elts {A : Type} (arr : Z -> A) (i : Z) (n : nat) : list A :=
  match n with
  | 0%nat => []
  | S n2 => arr i :: get_array_elts arr (i + 1) n2
  end.

Lemma nth_get_array_elts:
  forall {A} (arr : Z -> A) i n ix d, (ix < n)%nat ->
  nth ix (get_array_elts arr i n) d = arr (i + Z.of_nat ix).
Proof.
  intros until n.
  generalize i.
  induction n.
  - intros.
    lia.
  - intros.
    simpl.
    destruct ix.
    + f_equal.
      lia.
    + simpl.
      rewrite IHn by lia.
      f_equal.
      lia.
Qed.

Definition arc_in_array : Type := ((Z -> Z) * Z * Z).
 
Definition arc_from_array (arc : arc_in_array) :=
  match arc with
  | (arr, i, j) => get_array_elts arr i (Z.to_nat (j - i))
  end.

Definition array_to_list (arr : Z -> tree) (n : Z) :=
  of_list (get_array_elts arr 0 (Z.to_nat n)).

Fixpoint lookup_tree (t : tree) (arc : list Z) : option Z :=
  match t with
  | Empty_Tree => None
  | Node ts v => match arc with
    | [] => Some v
    | ix :: ixs => lookup_tree (CN_Lib.nth_list_z dest_list_of_tree ix ts Empty_Tree) ixs
    end
  end.

Definition in_tree (t : tree) (arc : arc_in_array) : bool :=
  match lookup_tree t (arc_from_array arc) with
  | Some _ => true
  | None => false
  end.

Definition tree_v (t : tree) (arc : arc_in_array) : Z :=
  match lookup_tree t (arc_from_array arc) with
  | Some v => v
  | None => 0
  end.

