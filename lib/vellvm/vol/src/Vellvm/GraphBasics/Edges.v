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



(* Edges are defined by a set of 2 arcs and by a couple of vertices.    *)

(* The following notions are defined :                                  *)
(*      - E_set : a set of two reciprocal arcs,                         *)
(*              constructors : E_right, E_left;                         *)
(*      - Edge : a couple of vertices,                                  *)
(*              constructor : E_ends;                                   *)
(*      - E_eq : the equality on edges,                                 *)
(*              constructors : E_refl, E_rev.                           *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Arcs.

Section EDGE.

Inductive E_set (x y : Vertex) : A_set :=
  | E_right : E_set x y (A_ends x y)
  | E_left : E_set x y (A_ends y x).

Lemma E_set_eq : forall x y : Vertex, E_set x y = E_set y x.
Proof.
        intros; apply A_set_eq.
        split; intros.
        inversion H; [ apply E_left | apply E_right ].

        inversion H; [ apply E_left | apply E_right ].
Qed.

Lemma E_set_diff1 :
 forall x x' y y' : Vertex, x <> x' -> x <> y' -> E_set x y <> E_set x' y'.
Proof.
        intros; red in |- *; intros.
        absurd (E_set x y (A_ends x' y')).
        red in |- *; intros; inversion H2.
        elim H; trivial.

        elim H0; trivial.

        rewrite H1; apply E_right.
Qed.

Lemma E_set_diff2 :
 forall x x' y y' : Vertex, y <> x' -> y <> y' -> E_set x y <> E_set x' y'.
Proof.
        intros; rewrite (E_set_eq x y); apply E_set_diff1; auto.
Qed.

Lemma E_set_diff3 :
 forall x x' y y' : Vertex, x' <> x -> x' <> y -> E_set x y <> E_set x' y'.
Proof.
        intros; apply A_set_diff_commut; apply E_set_diff1; trivial.
Qed.

Lemma E_set_diff4 :
 forall x x' y y' : Vertex, y' <> x -> y' <> y -> E_set x y <> E_set x' y'.
Proof.
        intros; apply A_set_diff_commut; apply E_set_diff2; trivial.
Qed.

Lemma E_set_eq_diff :
 forall x x' y y' : Vertex, x = x' -> y <> y' -> E_set x y <> E_set x' y'.
Proof.
        intros; red in |- *; intros.
        absurd (E_set x y (A_ends x' y')).
        red in |- *; intros; inversion H2.
        elim H0; trivial.

        elim H0; rewrite H4; rewrite <- H5; auto.

        rewrite H1; apply E_right.
Qed.

Lemma E_set_diff_eq :
 forall x x' y y' : Vertex, x <> x' -> y = y' -> E_set x y <> E_set x' y'.
Proof.
        intros; rewrite (E_set_eq x y); rewrite (E_set_eq x' y');
         apply E_set_eq_diff; trivial.
Qed.

Lemma E_set_eq_dec :
 forall x x' y y' : Vertex,
 {E_set x y = E_set x' y'} + {E_set x y <> E_set x' y'}.
Proof.
        intros; case (V_eq_dec x x'); intros.
        case (V_eq_dec y y'); intros.
        left; rewrite e; rewrite e0; trivial.

        right; apply E_set_eq_diff; trivial.

        case (V_eq_dec x y'); intros.
        case (V_eq_dec y x'); intros.
        left; rewrite e; rewrite e0; apply E_set_eq.

        right; rewrite (E_set_eq x y); apply E_set_diff_eq; trivial.

        right; apply E_set_diff1; trivial.
Qed.

Lemma E_not_set_eq123 :
 forall x y z t : Vertex, x <> z -> y <> z -> ~ E_set x y (A_ends z t).
Proof.
        red in |- *; intros.
        inversion H1.
        elim H; trivial.

        elim H0; trivial.
Qed.

Lemma E_not_set_eq14 :
 forall x y z : Vertex, x <> z -> ~ E_set x y (A_ends y z).
Proof.
        red in |- *; intros.
        inversion H0.
        elim H; rewrite H2; trivial.

        elim H; trivial.
Qed.

Lemma E_not_set_eq24 :
 forall x y z : Vertex, y <> z -> ~ E_set x y (A_ends x z).
Proof.
        red in |- *; intros.
        inversion H0.
        elim H; trivial.

        elim H; rewrite H2; trivial.
Qed.

End EDGE.

Section LIST_OF_EDGES.

Inductive Edge : Set :=
    E_ends : Vertex -> Vertex -> Edge.

Inductive E_eq : Edge -> Edge -> Prop :=
  | E_refl : forall u : Edge, E_eq u u
  | E_rev : forall x y : Vertex, E_eq (E_ends x y) (E_ends y x).

Definition E_list := list Edge.

Definition E_nil := nil (A:=Edge).

Lemma E_eq_dec : forall u v : Edge, {E_eq u v} + {~ E_eq u v}.
Proof.
        simple destruct u; intros a b; simple destruct v; intros c d.
        case (V_eq_dec a c); intros.
        case (V_eq_dec b d); intros.
        left; rewrite e; rewrite e0; apply E_refl.

        right; red in |- *; intros; inversion H.
        elim n; trivial.

        elim n; rewrite H3; rewrite <- H4; auto.

        case (V_eq_dec a d); intros.
        case (V_eq_dec b c); intros.
        left; rewrite e; rewrite e0; apply E_rev.

        right; red in |- *; intros; inversion H.
        elim n; trivial.

        elim n0; trivial.

        right; red in |- *; intros; inversion H.
        elim n; trivial.

        elim n0; trivial.
Qed.

Fixpoint E_in (u : Edge) (l : E_list) {struct l} : Prop :=
  match l with
  | nil => False
  | v :: l' => if E_eq_dec u v then True else E_in u l'
  end.

Lemma E_add_edge :
 forall (a : A_set) (x y : Vertex),
 A_union (E_set x y) a =
 A_union (A_single (A_ends x y)) (A_union (A_single (A_ends y x)) a).
Proof.
        intros; apply A_set_eq.
        split; intros.
        inversion_clear H.
        inversion_clear H0.
        apply A_in_left; apply A_in_single.

        apply A_in_right; apply A_in_left; apply A_in_single.

        do 2 apply A_in_right; trivial.

        inversion_clear H.
        inversion_clear H0.
        apply A_in_left; apply E_right.

        inversion_clear H0.
        inversion_clear H.
        apply A_in_left; apply E_left.

        apply A_in_right; trivial.
Qed.

End LIST_OF_EDGES.

Section E_PROPERTIES.

Lemma E_inclusion :
 forall (a : A_set) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x) -> A_included (E_set x y) a.
Proof.
        unfold A_included, Included, Ensembles.Included in |- *; intros.
        inversion H1; auto.
Qed.

Lemma E_union_absorb :
 forall (a : A_set) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x) -> A_union (E_set x y) a = a.
Proof.
        intros; apply A_union_absorb.
        apply E_inclusion; auto.
Qed.

Lemma E_inter_empty :
 forall x x' y y' : Vertex,
 E_set x y <> E_set x' y' -> A_inter (E_set x y) (E_set x' y') = A_empty.
Proof.
        intros; apply A_set_eq; split; intros.
        inversion H0.
        elim H; generalize H2; inversion H1; intros.
        inversion H5.
        trivial.

        apply E_set_eq.

        inversion H5.
        apply E_set_eq.

        trivial.

        inversion H0.
Qed.

Lemma E_set_disjoint :
 forall (x y : Vertex) (a : A_set),
 ~ a (A_ends x y) -> ~ a (A_ends y x) -> A_inter (E_set x y) a = A_empty.
Proof.
        intros; apply A_set_eq; split; intros.
        inversion H1.
        generalize H3; inversion H2; intros.
        absurd (a (A_ends x y)); trivial.

        absurd (a (A_ends y x)); trivial.

        inversion H1.
Qed.

Lemma A_in_union_edge :
 forall (x y x' y' : Vertex) (a : A_set),
 A_union (E_set x y) a (A_ends x' y') ->
 ~ E_set x y (A_ends x' y') -> a (A_ends x' y').
Proof.
        intros; inversion H.
        absurd (E_set x y (A_ends x' y')); trivial.

        trivial.
Qed.

Lemma A_union_edge_edge :
 forall (a a' : A_set) (x y : Vertex),
 ~ a' (A_ends x y) ->
 ~ a' (A_ends y x) ->
 a = A_empty ->
 A_union (E_set x y) a = A_union (E_set x y) a' -> A_empty = a'.
Proof.
        intros; apply A_union_inversion with (E := E_set x y).
        apply A_inter_empty.

        apply E_set_disjoint; trivial.

        rewrite <- H1; trivial.
Qed.

Lemma E_eq_not_in :
 forall (a : A_set) (x y x' y' : Vertex),
 ~ a (A_ends x y) ->
 ~ a (A_ends y x) -> E_set x y = E_set x' y' -> ~ a (A_ends x' y').
Proof.
        intros.
        generalize (A_eq_set _ _ H1 (A_ends x y) (E_right x y)); intros.
        inversion H2; trivial.
Qed.

Lemma E_eq_not_in' :
 forall (a : A_set) (x y x' y' : Vertex),
 ~ a (A_ends x y) ->
 ~ a (A_ends y x) -> E_set x y = E_set x' y' -> ~ a (A_ends y' x').
Proof.
        intros.
        generalize (A_eq_set _ _ H1 (A_ends x y) (E_right x y)); intros.
        inversion H2; trivial.
Qed.

End E_PROPERTIES.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/Vminus/GraphBasics" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
