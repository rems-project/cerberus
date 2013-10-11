(*
LR(1) parser validator
Copyright (C) 2011 INRIA

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>

Jacques-Henri Jourdan <jacques-henri.jourdan@ens.fr>
*)

Require Import NArith.
Require Import Omega.
Require Import List.
Require Import Syntax.
Require Import Relations.
Require Import RelationClasses.

Local Obligation Tactic := intros.

(** A comparable type is equiped with a [compare] function, that define an order
   relation. **)
Class Comparable (A:Type) := {
  compare : A -> A -> comparison;
  compare_antisym : forall x y, CompOpp (compare x y) = compare y x;
  compare_trans :  forall x y z c,
    (compare x y) = c -> (compare y z) = c -> (compare x z) = c
}.

Theorem compare_refl {A:Type} (C: Comparable A) :
  forall x, compare x x = Eq.
Proof.
intros.
pose proof (compare_antisym x x).
destruct (compare x x); intuition; try discriminate.
Qed.

(** The corresponding order is a strict order. **)
Definition comparableLt {A:Type} (C: Comparable A) : relation A :=
  fun x y => compare x y = Lt.

Instance ComparableLtStrictOrder {A:Type} (C: Comparable A) :
  StrictOrder (comparableLt C).
Proof.
apply Build_StrictOrder.
unfold Irreflexive, Reflexive, complement, comparableLt.
intros.
pose proof H.
rewrite <- compare_antisym in H.
rewrite H0 in H.
discriminate H.
unfold Transitive, comparableLt.
intros x y z.
apply compare_trans.
Qed.

(** nat is comparable. **)
Program Instance natComparable : Comparable nat :=
  { compare := nat_compare }.
Next Obligation.
symmetry.
destruct (nat_compare x y)  as [] _eqn.
rewrite nat_compare_eq_iff in Heqc.
destruct Heqc.
rewrite nat_compare_eq_iff.
trivial.
rewrite <- nat_compare_lt in *.
rewrite <- nat_compare_gt in *.
trivial.
rewrite <- nat_compare_lt in *.
rewrite <- nat_compare_gt in *.
trivial.
Qed.
Next Obligation.
destruct c.
rewrite nat_compare_eq_iff in *; destruct H; assumption.
rewrite <- nat_compare_lt in *.
apply (lt_trans _ _ _ H H0).
rewrite <- nat_compare_gt in *.
apply (gt_trans _ _ _ H H0).
Qed.

(** A pair of comparable is comparable. **)
Program Instance PairComparable {A:Type} (CA:Comparable A) {B:Type} (CB:Comparable B) :
  Comparable (A*B) :=
  { compare := fun x y =>
      let (xa, xb) := x in let (ya, yb) := y in
      match compare xa ya return comparison with
        | Eq => compare xb yb
        | x => x
      end }.
Next Obligation.
destruct x, y.
rewrite <- (compare_antisym a a0).
rewrite <- (compare_antisym b b0).
destruct (compare a a0); intuition.
Qed.
Next Obligation.
destruct x, y, z.
destruct (compare a a0) as [] _eqn, (compare a0 a1) as [] _eqn;
try (rewrite <- H0 in H; discriminate);
try (destruct (compare a a1) as [] _eqn;
  try (rewrite <- compare_antisym in Heqc0;
         rewrite CompOpp_iff in Heqc0;
         rewrite (compare_trans _ _ _  _ Heqc0 Heqc2) in Heqc1;
         discriminate);
  try (rewrite <- compare_antisym in Heqc1;
         rewrite CompOpp_iff in Heqc1;
         rewrite (compare_trans _ _ _ _ Heqc2 Heqc1) in Heqc0;
         discriminate);
  assumption);
rewrite (compare_trans _ _ _ _ Heqc0 Heqc1);
try assumption.
apply (compare_trans _ _ _ _ H H0).
Qed.

(** Special case of comparable, where equality is usual equality. **)
Class ComparableUsualEq {A:Type} (C: Comparable A) :=
  compare_eq : forall x y, compare x y = Eq -> x = y.

(** Boolean equality for a [Comparable]. **)
Definition compare_eqb {A:Type} {C:Comparable A} (x y:A) :=
  match compare x y with
    | Eq => true
    | _ => false
  end.

Theorem compare_eqb_iff {A:Type} {C:Comparable A} {U:ComparableUsualEq C} :
  forall x y, compare_eqb x y = true <-> x = y.
Proof.
unfold compare_eqb.
intuition.
apply compare_eq.
destruct (compare x y); intuition; discriminate.
destruct H.
rewrite compare_refl; intuition.
Qed.

(** [Comparable] provides a decidable equality. **)
Definition compare_eqdec {A:Type} {C:Comparable A} {U:ComparableUsualEq C} (x y:A):
  {x = y} + {x <> y}.
Proof.
destruct (compare x y) as [] _eqn; [left; apply compare_eq; intuition | ..];
  right; intro; destruct H; rewrite compare_refl in Heqc; discriminate.
Defined.

Instance NComparableUsualEq : ComparableUsualEq natComparable := nat_compare_eq.

(** A pair of ComparableUsualEq is ComparableUsualEq **)
Instance PairComparableUsualEq
  {A:Type} {CA:Comparable A} (UA:ComparableUsualEq CA)
  {B:Type} {CB:Comparable B} (UB:ComparableUsualEq CB) :
    ComparableUsualEq (PairComparable CA CB).
Proof.
intros x y; destruct x, y; simpl.
pose proof (compare_eq a a0); pose proof (compare_eq b b0).
destruct (compare a a0); try discriminate.
intuition.
destruct H2, H0.
reflexivity.
Qed.

(** An [Finite] type is a type with the list of all elements. **)
Class Finite (A:Type) := {
  all_list : list A;
  all_list_forall : forall x:A, In x all_list
}.

(** An alphabet is both [ComparableUsualEq] and [Finite]. **)
Class Alphabet (A:Type) := {
  AlphabetComparable :> Comparable A;
  AlphabetComparableUsualEq :> ComparableUsualEq AlphabetComparable;
  AlphabetFinite :> Finite A
}.

(** The [Numbered] class provides a conveniant way to build [Alphabet] instances,
   with a good computationnal complexity. It is mainly a injection from it to [N] **)
Class Numbered (A:Type) := {
  injN : A -> N;
  surjN : N -> A;
  surjN_injN_compat : forall x, surjN (injN x) = x;
  injN_bound : N;
  injN_bound_spec : forall x, (injN x < injN_bound)%N
}.

Program Instance NumberedAlphabet {A:Type} (N:Numbered A) : Alphabet A :=
  { AlphabetComparable :=
      {| compare := fun x y => Ncompare (injN x) (injN y) |};
    AlphabetFinite :=
      {| all_list := Nrect _ [] (fun n => cons (surjN n)) injN_bound |} }.
Next Obligation.
apply Ncompare_antisym.
Qed.
Next Obligation.
pose proof (Ncompare_spec (injN x) (injN y)).
pose proof (Ncompare_spec (injN y) (injN z)).
rewrite H in H1; rewrite H0 in H2.
destruct H1; inversion H2.
rewrite H1; rewrite H3.
apply Ncompare_refl.
apply (Nlt_trans _ _ _ H1 H3).
apply CompOpp_inj.
rewrite Ncompare_antisym.
apply (Nlt_trans _ _ _ H3 H1).
Qed.
Next Obligation.
intros x y.
simpl.
rewrite Ncompare_eq_correct.
intro.
rewrite <- (surjN_injN_compat x).
rewrite H.
apply surjN_injN_compat.
Qed.
Next Obligation.
pose proof (injN_bound_spec x).
revert H.
induction injN_bound using Nind.
destruct (injN x); discriminate.
intros.
rewrite Nrect_step.
pose proof (Ncompare_spec (injN x) n).
unfold Nlt in IHn.
destruct H0.
rewrite <- H0.
left; apply surjN_injN_compat.
intuition.
elimtype False.
pose proof (Z_of_N_lt _ _ H).
rewrite Z_of_N_succ in H1.
pose proof (Z_of_N_lt _ _ H0).
omega.
Qed.

(** Previous class instances for [option A] **)
Program Instance OptionComparable {A:Type} (C:Comparable A) : Comparable (option A) :=
  { compare := fun x y =>
      match x, y return comparison with
        | None, None => Eq
        | None, Some _ => Lt
        | Some _, None => Gt
        | Some x, Some y => compare x y
      end }.
Next Obligation.
destruct x, y; intuition.
apply compare_antisym.
Qed.
Next Obligation.
destruct x, y, z; try now intuition;
try (rewrite <- H in H0; discriminate).
apply (compare_trans _ _ _ _ H H0).
Qed.

Instance OptionComparableUsualEq {A:Type} {C:Comparable A} (U:ComparableUsualEq C) :
  ComparableUsualEq (OptionComparable C).
Proof.
intros x y.
destruct x, y; intuition; try discriminate.
rewrite (compare_eq a a0); intuition.
Qed.

Program Instance OptionFinite {A:Type} (E:Finite A) : Finite (option A) :=
  { all_list := None :: map Some all_list }.
Next Obligation.
destruct x; intuition.
right.
apply in_map.
apply all_list_forall.
Defined.

(** Definitions of [FSet]/[FMap] from [Comparable] **)
Require Import OrderedType.
Require Import OrderedTypeAlt.
Require FSetAVL.
Require FMapAVL.

Module Type ComparableM.
  Parameter t : Type.
  Declare Instance tComparable : Comparable t.
End ComparableM.

Module OrderedTypeAlt_from_ComparableM (C:ComparableM) <: OrderedTypeAlt.
  Definition t := C.t.
  Definition compare : t -> t -> comparison := compare.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym x y : (y?=x) = CompOpp (x?=y).
  Proof. exact (Logic.eq_sym (compare_antisym x y)). Qed.
  Lemma compare_trans c x y z :
    (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
  apply compare_trans.
  Qed.
End OrderedTypeAlt_from_ComparableM.

Module OrderedType_from_ComparableM (C:ComparableM) <: OrderedType.
  Module Alt := OrderedTypeAlt_from_ComparableM C.
  Include (OrderedType_from_Alt Alt).
End OrderedType_from_ComparableM.
