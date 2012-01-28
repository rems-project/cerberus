(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* A set with elements in U, is defined by its belonging relation,      *)
(* the equality is defined by the extensionality axiom.                 *)

(* The following notions are defined :                                  *)
(*      - U_set :  set with elements in U,                              *)
(*      - U_set_eq : 2 sets with same elements are equals,              *)
(*      - Empty :  set with no elements,                                *)
(*              no constructors                                         *)
(*      - Full :  set with all the elements,                            *)
(*              constructor : In_full                                   *)
(*      - Single : set with a unique element {x},                       *)
(*              constructor : In_single                                 *)
(*      - Included : like imply,                                        *)
(*      - Union : binary operation like or,                             *)
(*              constructors : In_left, In_right.                       *)
(*      - Inter : binary operation like and,                            *)
(*              constructors : In_inter.                                *)

Require Export Omega.
Require Export Peano_dec.
Require Import Ensembles.
Require Import Constructive_sets.

Section U_SETS.

Variable U : Type.

Definition U_set := Ensemble U.

Lemma U_set_eq : forall E F : U_set, (forall x : U, E x <-> F x) -> E = F.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros; intro x; eapply H; eauto.
Qed.

Lemma U_eq_set : forall E F : U_set, E = F -> forall x : U, E x -> F x.
Proof.
  intros; rewrite <- H; trivial.
Qed.

Lemma U_set_eq_commut : forall E F : U_set, E = F -> F = E.
Proof.
  auto.
Qed.

Lemma U_set_diff_commut : forall E F : U_set, E <> F -> F <> E.
Proof.
  intros; red in |- *; intros.
  elim H; apply U_set_eq_commut; trivial.
Qed.

Definition Empty := Empty_set U.

Definition Full := Full_set U.

Definition Single := Singleton U.

Definition In_single := In_singleton.

Lemma Single_equal : forall x y : U, Single x y -> x = y.
Proof.
  intros; inversion H; trivial.
Qed.

Lemma Single_equal_single : forall x y : U, Single x = Single y -> x = y.
Proof.
  intros; generalize (U_eq_set _ _ H x).
  intros; elim H0.
  trivial.
  
  apply In_singleton.
Qed.

Lemma Empty_nothing : forall x : U, ~ Empty x.
Proof.
  unfold Empty. tauto.
Qed.

Lemma U_set_diff : forall E F : U_set, (exists x : U, E x /\ ~ F x) -> E <> F.
Proof.
        intros; red in |- *; intros.
        elim H; intros.
        elim H1; intros.
        elim H3; rewrite <- H0; auto.
Qed.

Lemma Included_single :
 forall (E : U_set) (x : U), E x -> Included _ (Single x) E.
Proof.
        unfold Included in |- *; intros.
        inversion H0; rewrite <- H1; trivial.
Qed.

Definition In_right := Union_intror.
Definition In_left := Union_introl.

Lemma Union_eq :
 forall E F E' F' : U_set, E = E' -> F = F' -> Union _ E F = Union _ E' F'.
Proof.
        intros; elim H.
        elim H0; trivial.
Qed.

Lemma Union_neutral : forall e : U_set, Union _ Empty e = e.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        inversion H0.

        trivial.

        apply Union_intror; trivial.
Qed.

Lemma Union_commut : forall e1 e2 : U_set, Union _ e1 e2 = Union _ e2 e1.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; [ apply Union_intror | apply Union_introl ]; trivial.

        inversion H; [ apply Union_intror | apply Union_introl ]; trivial.
Qed.

Lemma Union_assoc : forall e1 e2 e3 : U_set, 
  Union _ (Union _ e1 e2) e3 = Union _ e1 (Union _ e2 e3).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        inversion H0.
        apply Union_introl; trivial.

        apply Union_intror; apply Union_introl; trivial.

        apply Union_intror; apply Union_intror; trivial.

        inversion H.
        apply Union_introl; apply Union_introl; trivial.

        inversion H0.
        apply Union_introl; apply Union_intror; trivial.

        apply Union_intror; trivial.
Qed.

Lemma Not_union :
 forall (E1 E2 : U_set) (x : U), ~ E1 x -> ~ E2 x -> ~ Union _ E1 E2 x.
Proof.
        intros; red in |- *; intros.
        inversion H1.
        elim H; trivial.

        elim H0; trivial.
Qed.

Lemma Union_dec :
 forall (e1 e2 : U_set) (x : U),
 {e1 x} + {~ e1 x} -> {e2 x} + {~ e2 x} -> Union _ e1 e2 x -> {e1 x} + {e2 x}.
Proof.
        intros; case H.
        left; trivial.

        intros; case H0; intros.
        right; trivial.

        absurd (Union _ e1 e2 x).
        apply Not_union; trivial.

        trivial.
Qed.

Lemma Included_union : forall E F : U_set, Included _ E (Union _ E F).
Proof.
        unfold Included in |- *; intros.
        apply Union_introl; trivial.
Qed.

Lemma Union_absorb : forall E F : U_set, Included _ E F -> Union _ E F = F.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0; subst; auto.
        apply H; auto.

        apply Union_intror; trivial.
Qed.

Definition Inter := Intersection U.

Definition In_inter := Intersection_intro.

Lemma Inter_eq :
 forall E F E' F' : U_set, E = E' -> F = F' -> Inter E F = Inter E' F'.
Proof.
        intros; elim H.
        elim H0; trivial.
Qed.

Lemma Inter_neutral : forall e : U_set, Inter Full e = e.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        apply Intersection_intro.
        apply Full_intro; trivial.

        trivial.
Qed.

Lemma Inter_empty : forall e : U_set, Inter e Empty = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        inversion H.
Qed.

Lemma Inter_commut : forall e1 e2 : U_set, Inter e1 e2 = Inter e2 e1.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; apply Intersection_intro; trivial.

        inversion H; apply Intersection_intro; trivial.
Qed.

Lemma Inter_assoc :
 forall e1 e2 e3 : U_set, Inter (Inter e1 e2) e3 = Inter e1 (Inter e2 e3).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; inversion H0.
        apply Intersection_intro; trivial.
        apply Intersection_intro; trivial.

        inversion H; inversion H1.
        apply Intersection_intro; trivial.
        apply Intersection_intro; trivial.
Qed.

Lemma Not_inter : forall (E1 E2 : U_set) (x : U), ~ E1 x -> ~ Inter E1 E2 x.
Proof.
        intros; red in |- *; intros.
        inversion H0.
        elim H; trivial.
Qed.

Lemma Included_inter : forall E F : U_set, Included _ (Inter E F) E.
Proof.
        unfold Included in |- *; intros.
        inversion H; trivial.
Qed.

Lemma Inter_absorb : forall E F : U_set, Included _ E F -> Inter E F = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0; auto.

        apply Intersection_intro; auto.
Qed.

Definition Differ := Setminus U.

Lemma Differ_E_E : forall E : U_set, Differ E E = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        absurd (E x); trivial.

        inversion H.
Qed.

Lemma Differ_empty : forall E : U_set, Differ E Empty = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        split; auto.
          intro J. inversion J.
Qed.

Lemma Union_differ_inter :
 forall (E F : U_set)
 (H: forall x : U, {F x} + {~ F x}), Union _ (Differ E F) (Inter E F) = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0; inversion H1; trivial.

        case (H x); intros.
          apply Union_intror; apply Intersection_intro; trivial.
          apply Union_introl; apply Setminus_intro; trivial.
Qed.

        Section MIXED_PROPERTIES.

Lemma Distributivity_inter_union :
  forall E F G : U_set, Inter E (Union _ F G) = Union _ (Inter E F) (Inter E G).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; inversion H1.
        apply Union_introl; apply Intersection_intro; auto.

        apply Union_intror; apply Intersection_intro; auto.

        inversion H; inversion H0.
        apply Intersection_intro.
        trivial.

        apply Union_introl; trivial.

        apply Intersection_intro.
        trivial.

        apply Union_intror; trivial.
Qed.

Lemma Distributivity_union_inter :
 forall E F G : U_set, Union _ E (Inter F G) = Inter (Union _ E F) (Union _ E G).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        apply Intersection_intro; apply Union_introl; trivial.

        inversion H0; apply Intersection_intro; apply Union_intror; trivial.

        inversion H.
        inversion H0.
        apply Union_introl; trivial.

        inversion H1.
        apply Union_introl; trivial.

        apply Union_intror; apply Intersection_intro; trivial.
Qed.

Lemma Union_inversion :
 forall E F G : U_set,
 Inter E F = Empty -> Inter E G = Empty -> Union _ E F = Union _ E G -> F = G.
Proof.
        intros; apply U_set_eq; split; intros.
        generalize (Union_intror _ E F x H2).
        rewrite H1; intros.
        inversion H3.
        absurd (Inter E F x).
        rewrite H. apply Empty_nothing.

        apply Intersection_intro; auto.

        trivial.

        generalize (Union_intror _ E G x H2).
        rewrite <- H1; intros.
        inversion H3.
        absurd (Inter E G x).
        rewrite H0. apply Empty_nothing.

        apply Intersection_intro; auto.

        trivial.
Qed.

Lemma Union_inversion2 :
 forall E F G H : U_set,
 Inter E F = Empty ->
 Inter E G = Empty ->
 Inter G H = Empty -> Union _ E F = Union _ G H -> F = Union _ G (Inter F H).
Proof.
        intros; apply U_set_eq; split; intros.
        generalize (Union_intror _ E F x H4).
        rewrite H3; intros.
        inversion H5.
        apply Union_introl; trivial.

        apply Union_intror; apply Intersection_intro; trivial.

        inversion H4.
        generalize (Union_introl _ G H x H5).
        rewrite <- H3; intros.
        inversion H7.
        absurd (Inter E G x).
        rewrite H1. apply Empty_nothing.

        apply Intersection_intro; trivial.

        trivial.

        inversion H5; trivial.
Qed.

Lemma Single_disjoint :
 forall (x : U) (E : U_set), ~ E x -> Inter (Single x) E = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0.
        inversion H1; absurd (E x).
        trivial.

        rewrite H4; trivial.

        inversion H0.
Qed.

Lemma Single_single_disjoint :
 forall x y : U, x <> y -> Inter (Single x) (Single y) = Empty.
Proof.
        intros; apply Single_disjoint.
        red in |- *; intros H0; elim H; inversion H0; trivial.
Qed.

Lemma Union_single_single :
 forall (e : U_set) (x y : U),
 x <> y ->
 ~ e y -> Union _ (Single x) (Single y) = Union _ (Single y) e -> e = Single x.
Proof.
        intros; symmetry  in |- *; apply (Union_inversion (Single y)).
        apply Single_single_disjoint; auto.

        apply Single_disjoint; trivial.

        rewrite Union_commut; trivial.
Qed.

        End MIXED_PROPERTIES.

Definition Included := Ensembles.Included U.
Definition Union := Ensembles.Union U.

End U_SETS.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
