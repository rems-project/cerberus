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



(* Usual notions of neighborhood and degree in a graph, direcetd or not.*)

(* The following notions are defined :                                  *)
(*      - In_neighbor : relation between 2 vertices of a digraph;       *)
(*      - Out_neighbor : id;                                            *)
(*      - In_neighborhood : list of in_neighbors of a vertex;           *)
(*      - Out_neighborhood : list of out_neighbors of a vertex;         *)
(*      - neighbor : relation between 2 vertices;                       *)
(*      - neighborhood : list of neighbors of a vertex;                 *)
(*      - In_degree : nuber of in_neighbors of a vertex;                *)
(*      - Out_degree : number of out_neighbors of a vertex.             *)
(*      - degree : number of neighbors of a vertex;                     *)
(*      - isolated : vertex without neighbor;                           *)
(*      - pendant : vertex with only one neighbor.                      *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Graphs.

Section NEIGHBOR.

Variable v : V_set.

Variable a : A_set.

Definition In_neighbor (x y : Vertex) := a (A_ends y x).

Definition Out_neighbor (x y : Vertex) := a (A_ends x y).

Definition Neighbor (x y : Vertex) := A_included (E_set x y) a.

Lemma neighbor_in_neighbor :
 forall x y : Vertex, Neighbor x y -> In_neighbor x y.
Proof.
        unfold Neighbor, A_included, Included, In_neighbor in |- *; intros.
        apply H; apply E_left.
Qed.

Lemma neighbor_out_neighbor :
 forall x y : Vertex, Neighbor x y -> Out_neighbor x y.
Proof.
        unfold Neighbor, A_included, Included, Out_neighbor in |- *; intros.
        apply H; apply E_right.
Qed.

Lemma In_and_out_neighbor :
 forall x y : Vertex, In_neighbor x y -> Out_neighbor x y -> Neighbor x y.
Proof.
        unfold Neighbor, A_included, Included, Ensembles.Included, In_neighbor, 
         Out_neighbor in |- *; intros.
        inversion H1; auto.
Qed.

End NEIGHBOR.

Section DEGREE.

Fixpoint In_neighborhood (x : Vertex) (v : V_set) (a : A_set)
 (d : Digraph v a) {struct d} : V_list :=
  match d with
  | D_empty => V_nil
  | D_vertex v' a' d' x' _ => In_neighborhood x v' a' d'
  | D_arc v' a' d' x' y' _ _ _ =>
      if V_eq_dec x y'
      then x' :: In_neighborhood x v' a' d'
      else In_neighborhood x v' a' d'
  | D_eq v' _ a' _ _ _ d' => In_neighborhood x v' a' d'
  end.

Fixpoint Out_neighborhood (x : Vertex) (v : V_set) 
 (a : A_set) (d : Digraph v a) {struct d} : V_list :=
  match d with
  | D_empty => V_nil
  | D_vertex v' a' d' x' _ => Out_neighborhood x v' a' d'
  | D_arc v' a' d' x' y' _ _ _ =>
      if V_eq_dec x x'
      then y' :: Out_neighborhood x v' a' d'
      else Out_neighborhood x v' a' d'
  | D_eq v' _ a' _ _ _ d' => Out_neighborhood x v' a' d'
  end.

Fixpoint neighborhood (x : Vertex) (v : V_set) (a : A_set) 
 (g : Graph v a) {struct g} : V_list :=
  match g with
  | G_empty => V_nil
  | G_vertex v' a' g' x' _ => neighborhood x v' a' g'
  | G_edge v' a' g' x' y' _ _ _ _ _ =>
      if V_eq_dec x x'
      then y' :: neighborhood x v' a' g'
      else
       if V_eq_dec x y'
       then x' :: neighborhood x v' a' g'
       else neighborhood x v' a' g'
  | G_eq v' _ a' _ _ _ g' => neighborhood x v' a' g'
  end.

Fixpoint In_degree (x : Vertex) (v : V_set) (a : A_set) 
 (d : Digraph v a) {struct d} : nat :=
  match d with
  | D_empty => 0
  | D_vertex v' a' d' x' _ => In_degree x v' a' d'
  | D_arc v' a' d' x' y' _ _ _ =>
      if V_eq_dec x y'
      then S (In_degree x v' a' d')
      else In_degree x v' a' d'
  | D_eq v' _ a' _ _ _ d' => In_degree x v' a' d'
  end.

Lemma In_degree_neighborhood :
 forall (x : Vertex) (v : V_set) (a : A_set) (d : Digraph v a),
 In_degree x v a d = length (In_neighborhood x v a d).
Proof.
        simple induction d; simpl in |- *; intros.
        trivial.

        trivial.

        case (V_eq_dec x y); rewrite H; auto.

        trivial.
Qed.

Fixpoint Out_degree (x : Vertex) (v : V_set) (a : A_set) 
 (d : Digraph v a) {struct d} : nat :=
  match d with
  | D_empty => 0
  | D_vertex v' a' d' x' _ => Out_degree x v' a' d'
  | D_arc v' a' d' x' y' _ _ _ =>
      if V_eq_dec x x'
      then S (Out_degree x v' a' d')
      else Out_degree x v' a' d'
  | D_eq v' _ a' _ _ _ d' => Out_degree x v' a' d'
  end.

Lemma Out_degree_neighborhood :
 forall (x : Vertex) (v : V_set) (a : A_set) (d : Digraph v a),
 Out_degree x v a d = length (Out_neighborhood x v a d).
Proof.
        simple induction d; simpl in |- *; intros.
        trivial.

        trivial.

        case (V_eq_dec x x0); rewrite H; auto.

        trivial.
Qed.

Fixpoint degree (x : Vertex) (v : V_set) (a : A_set) 
 (g : Graph v a) {struct g} : nat :=
  match g with
  | G_empty => 0
  | G_vertex v' a' g' x' _ => degree x v' a' g'
  | G_edge v' a' g' x' y' _ _ _ _ _ =>
      if V_eq_dec x x'
      then S (degree x v' a' g')
      else
	if V_eq_dec x y'
	then S (degree x v' a' g')
	else degree x v' a' g'
  | G_eq v' _ a' _ _ _ g' => degree x v' a' g'
  end.

Lemma Degree_neighborhood :
 forall (x : Vertex) (v : V_set) (a : A_set) (g : Graph v a),
 degree x v a g = length (neighborhood x v a g).
Proof.
        simple induction g; simpl in |- *; intros.
        trivial.

        trivial.

        case (V_eq_dec x x0); intros.
        rewrite H; auto.

        case (V_eq_dec x y); rewrite H; auto.

        trivial.
Qed.

End DEGREE.

Section REMARKABLE_DEGREE.

Definition isolated (x : Vertex) (v : V_set) (a : A_set) 
  (g : Graph v a) := forall y : Vertex, ~ a (A_ends x y).

Lemma Degree_isolated :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex),
 isolated x v a g -> degree x v a g = 0.
Proof.
        unfold isolated in |- *; simple induction g; simpl in |- *; intros.
        trivial.

        auto.

        case (V_eq_dec x0 x); intros.
        absurd (A_union (E_set x y) a0 (A_ends x0 y)).
        auto.

        rewrite e; apply A_in_left; apply E_right.

        case (V_eq_dec x0 y); intros.
        absurd (A_union (E_set x y) a0 (A_ends x0 x)).
        auto.

        rewrite e; apply A_in_left; apply E_left.

        apply (H x0); red in |- *; intros.
        elim (H0 y0); apply A_in_right; trivial.

        apply (H x); rewrite e0; trivial.
Qed.

Definition pendant (x : Vertex) (v : V_set) (a : A_set) 
  (g : Graph v a) :=
  exists2 y : Vertex,
    a (A_ends x y) & (forall z : Vertex, a (A_ends x z) -> z = y).

Lemma Degree_pendant :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex),
 pendant x v a g -> degree x v a g = 1.
Proof.
        unfold pendant in |- *; simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        rewrite (Degree_isolated v0 a0 d x0).
        trivial.

        elim H0; rewrite e; intros.
        unfold isolated in |- *; red in |- *; intros.
        absurd (y0 = x1).
        red in |- *; intros.
        absurd (y = x1).
        red in |- *; intros; elim n0.
        rewrite H5; rewrite <- H4; trivial.

        apply H2; apply A_in_left; apply E_right.

        apply H2; apply A_in_right; trivial.

        case (V_eq_dec x0 y); intros.
        rewrite (Degree_isolated v0 a0 d x0).
        trivial.

        elim H0; rewrite e; intros.
        unfold isolated in |- *; red in |- *; intros.
        absurd (y0 = x1).
        red in |- *; intros.
        absurd (x = x1).
        red in |- *; intros; elim n1.
        rewrite H5; rewrite <- H4; trivial.

        apply H2; apply A_in_left; apply E_left.

        apply H2; apply A_in_right; trivial.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        intros; apply H2; apply A_in_right; trivial.

        apply H; rewrite e0; trivial.
Qed.

Lemma Degree_not_isolated :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex),
 (exists y : Vertex, a (A_ends x y)) -> degree x v a g > 0.
Proof.
        simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        omega.

        case (V_eq_dec x0 y); intros.
        omega.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        apply H; rewrite e0; trivial.
Qed.

Lemma Degree_not_pendant :
 forall (v : V_set) (a : A_set) (g : Graph v a) (x : Vertex),
 (exists2 y : Vertex,
    a (A_ends x y) & (exists2 z : Vertex, a (A_ends x z) & y <> z)) ->
 degree x v a g > 1.
Proof.
        simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        apply gt_n_S; apply Degree_not_isolated.
        elim H0; rewrite e; intros.
        case (V_eq_dec x1 y); intros.
        elim H2; rewrite e0; intros.
        split with x2.
        apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq24; auto.

        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq24; auto.

        case (V_eq_dec x0 y); intros.
        apply gt_n_S; apply Degree_not_isolated.
        elim H0; rewrite e; intros.
        case (V_eq_dec x x1); intros.
        elim H2; rewrite e0; intros.
        split with x2; apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq14; trivial.

        split with x1; apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq14; trivial.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        elim H2; intros.
        split with x2.
        apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq123; auto.

        trivial.

        apply H; rewrite e0; trivial.
Qed.

End REMARKABLE_DEGREE.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
