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



(* In a connected graph, each vertex is bound by a path to each other.  *)
(* We define first a connected, then prove this property.               *)

(* The following notion is defined :                                    *)
(*      - Connected : defined upon a set of vertices and a set of arcs, *)
(*              constructors : C_isolated, C_leaf, C_edge, C_eq.        *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Graphs.

Section CONNECTED.

Inductive Connected : V_set -> A_set -> Set :=
  | C_isolated : forall x : Vertex, Connected (V_single x) A_empty
  | C_leaf :
      forall (v : V_set) (a : A_set) (co : Connected v a) (x y : Vertex),
      v x ->
      ~ v y -> Connected (V_union (V_single y) v) (A_union (E_set x y) a)
  | C_edge :
      forall (v : V_set) (a : A_set) (co : Connected v a) (x y : Vertex),
      v x ->
      v y ->
      x <> y ->
      ~ a (A_ends x y) ->
      ~ a (A_ends y x) -> Connected v (A_union (E_set x y) a)
  | C_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Connected v a -> Connected v' a'.

Lemma Connected_not_empty :
 forall (v : V_set) (a : A_set), Connected v a -> v <> V_empty.
Proof.
        intros v a c; elim c; red in |- *; intros.
        elim (V_empty_nothing x); fold V_empty in |- *; rewrite <- H;
         apply V_in_single.
        elim (V_empty_nothing y); fold V_empty in |- *; rewrite <- H0;
         apply V_in_left; apply V_in_single.

        elim H; trivial.

        elim H; rewrite e; trivial.
Qed.

Lemma Connected_Isa_Graph :
 forall (v : V_set) (a : A_set), Connected v a -> Graph v a.
Proof.
        intros v a c; elim c; intros.
        apply G_eq with (v := V_union (V_single x) V_empty) (a := A_empty).
        rewrite V_union_commut; apply V_union_neutral.

        trivial.

        apply G_vertex.
        exact G_empty.

        compute in |- *. tauto.

        apply G_edge; intros.
        apply G_vertex; trivial.

        apply V_in_right; trivial.

        apply V_in_left; apply V_in_single.

        red in |- *; intros; elim n; rewrite <- H0; trivial.

        red in |- *; intros; elim n; apply (G_ina_inv2 _ _ H _ _ H0).

        red in |- *; intros; elim n; apply (G_ina_inv1 _ _ H _ _ H0).

        apply G_edge; trivial.

        apply G_eq with (v := v0) (a := a0); auto.
Qed.

Lemma C_v_dec :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x : Vertex),
 {v x} + {~ v x}.
Proof.
        intros; generalize (Connected_Isa_Graph v a c); intros g.
        apply (G_v_dec v a g x).
Qed.

Lemma C_a_dec :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x : Arc),
 {a x} + {~ a x}.
Proof.
        intros; generalize (Connected_Isa_Graph v a c); intros g.
        apply (G_a_dec v a g x).
Qed.

Lemma C_ina_inv1 :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 a (A_ends x y) -> v x.
Proof.
        intros; apply (G_ina_inv1 v a (Connected_Isa_Graph v a c) x y H).
Qed.

Lemma C_ina_inv2 :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 a (A_ends x y) -> v y.
Proof.
        intros; apply (G_ina_inv2 v a (Connected_Isa_Graph v a c) x y H).
Qed.

End CONNECTED.

Require Export Paths.

Section CONNECTED_BY_EDGES.

Remark V_included_union' : forall E F : V_set, V_included F (V_union E F).
Proof.
        intros; rewrite V_union_commut; apply V_included_union.
Qed.

Remark A_included_union' : forall E F : A_set, A_included F (A_union E F).
Proof.
        intros; rewrite A_union_commut; apply A_included_union.
Qed.

Lemma Connected_walk :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Walk v a x y vl el}}.
Proof.
        intros v a c; elim c; intros.
        split with V_nil; split with E_nil.
        inversion H.
        rewrite H1 in H0; inversion H0.
        apply W_null.
        apply V_in_single.

        case (V_union_single_dec _ _ _ n H0);
         case (V_union_single_dec _ _ _ n H1); intros.
        split with V_nil; split with E_nil.
        rewrite <- e; rewrite <- e0; apply W_null.
        apply V_in_left; apply V_in_single.

        elim (H x y0 v1 v2); intros.
        split with (x :: x1); elim p; intros.
        split with (E_ends y x :: x2); rewrite <- e; apply W_step.
        apply
         (Walk_subgraph v0 (V_union (V_single y) v0) a0
            (A_union (E_set x y) a0) x y0 x1 x2 p0).
        apply V_included_union'.

        apply A_included_union'.

        apply V_in_left; apply V_in_single.

        apply A_in_left; apply E_left.

        elim (H x0 x v2 v1); intros.
        split with (x1 ++ y0 :: V_nil); elim p; intros.
        split with (x2 ++ E_ends x y0 :: E_nil);
         apply Walk_append with (y := x).
        apply
         (Walk_subgraph _ (V_union (V_single y) v0) _
            (A_union (E_set x y) a0) _ _ _ _ p0).
        apply V_included_union'.

        apply A_included_union'.

        apply W_step.
        apply W_null.
        rewrite e; apply V_in_left; apply V_in_single.

        apply V_in_right; trivial.

        rewrite e; apply A_in_left; apply E_right.

        elim (H x0 y0 v3 v2); intros.
        split with x1; elim p; intros.
        split with x2;
         apply
          (Walk_subgraph _ (V_union (V_single y) v0) _
             (A_union (E_set x y) a0) _ _ _ _ p0).
        apply V_included_union'.

        apply A_included_union'.

        elim (H x0 y0 H0 H1); intros.
        split with x1; elim p; intros.
        split with x2;
         apply (Walk_subgraph _ v0 _ (A_union (E_set x y) a0) _ _ _ _ p0).
        unfold V_included, Included, Ensembles.Included in |- *; auto.

        apply A_included_union'.

        elim (H x y); intros.
        split with x0; elim p; intros.
        split with x1; apply Walk_eq with (v := v0) (a := a0); auto.

        rewrite e; trivial.

        rewrite e; trivial.
Qed.

Lemma Connected_path :
 forall (v : V_set) (a : A_set) (g : Connected v a) (x y : Vertex),
 v x -> v y -> {vl : V_list &  {el : E_list &  Path v a x y vl el}}.
Proof.
        intros; elim (Connected_walk v a g x y H H0); intros.
        elim p; intros.
        apply (Walk_to_path v a x y x0 x1 p0).
Qed.

End CONNECTED_BY_EDGES.

Section INVERSION_CONNECTED.

Lemma C_minus_isolated :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x : Vertex),
 v x ->
 (forall y : Vertex, ~ a (A_ends x y)) -> v = V_single x /\ a = A_empty.
Proof.
        intros v a c; elim c; intros.
        inversion H; auto.

        case (V_union_single_dec _ _ _ n H0); intros.
        elim (H1 x); rewrite e; apply A_in_left; apply E_left.

        generalize (A_not_in_union _ _ _ H1); intros.
        generalize (H x0 v2 H2); intros; decompose [and] H3.
        elim (H1 y); rewrite H4 in v1; inversion v1; apply A_in_left;
         apply E_right.

        generalize (A_not_in_union _ _ _ H1); intros.
        generalize (H x0 H0 H2); intros; decompose [and] H3.
        rewrite H4 in v1; inversion v1; rewrite H4 in v2; inversion v2.
        elim n; rewrite <- H6; trivial.

        rewrite <- e; rewrite <- e0; apply H.
        rewrite e; trivial.

        rewrite e0; trivial.
Qed.

Lemma C_minus_isolated_left :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x : Vertex),
 v x -> (forall y : Vertex, ~ a (A_ends x y)) -> v = V_single x.
Proof.
        intros; elim (C_minus_isolated v a c x); auto.
Qed.

Lemma C_minus_isolated_right :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x : Vertex),
 v x -> (forall y : Vertex, ~ a (A_ends x y)) -> a = A_empty.
Proof.
        intros; elim (C_minus_isolated v a c x); auto.
Qed.

Lemma C_pendant_isolated :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y z : Vertex),
 ~ v y ->
 (forall t : Vertex, A_union (E_set x y) a (A_ends z t) -> t = y) ->
 forall t : Vertex, ~ a (A_ends z t).
Proof.
        intros; red in |- *; intros; elim H.
        generalize (H0 t); intros.
        rewrite <- H2.
        apply (C_ina_inv2 _ _ c _ _ H1).

        apply A_in_right; trivial.
Qed.

Lemma E_pendant_quasi_isolated :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 v y ->
 ~ a (A_ends y x) ->
 (forall z : Vertex, A_union (E_set x y) a (A_ends y z) -> z = x) ->
 v = V_single y.
Proof.
        intros; apply (C_minus_isolated_left _ _ c y H).
        red in |- *; intros; elim H0; rewrite <- (H1 y0).
        trivial.

        apply A_in_right; trivial.
Qed.

Lemma E_not_eq_traversal_pendant :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y x' y' : Vertex),
 v x ->
 v y ->
 x <> y ->
 ~ a (A_ends x y) ->
 ~ a (A_ends y x) ->
 v x' ->
 v y' ->
 (forall z : Vertex, A_union (E_set x y) a (A_ends y' z) -> z = x') ->
 E_set x y <> E_set x' y'.
Proof.
        intros; red in |- *; intros.
        generalize H6; rewrite H7; intros.
        generalize (E_eq_not_in' _ _ _ _ _ H2 H3 H7); intros.
        generalize (E_pendant_quasi_isolated _ _ c x' y' H5 H9 H8); intros.
        elim H1.
        rewrite H10 in H; inversion H.
        rewrite H10 in H0; inversion H0.
        rewrite <- H11; trivial.
Qed.

Lemma C_minus_pendant :
 forall (v : V_set) (a : A_set) (c : Connected v a) (x y : Vertex),
 v x ->
 v y ->
 (forall z : Vertex, a (A_ends y z) -> z = x) ->
 forall (v' : V_set) (a' : A_set),
 ~ v' y ->
 v = V_union (V_single y) v' ->
 ~ a' (A_ends x y) ->
 ~ a' (A_ends y x) -> a = A_union (E_set x y) a' -> Connected v' a'.
Proof.
        intros v a c; elim c; intros.
        elim (A_empty_nothing (A_ends x0 y)).
        fold A_empty in |- *; rewrite H6; apply A_in_left; apply E_right.

        case (V_union_single_dec _ _ _ n H1); intros.
        apply C_eq with (v := v0) (a := a0).
        apply (V_union_inversion (V_single y)).
        apply V_single_disjoint; trivial.

        rewrite e; apply V_single_disjoint; trivial.

        rewrite <- e in H4; trivial.

        generalize (H2 x); rewrite e; intros.
        apply (A_union_inversion (E_set x y)).
        apply E_set_disjoint; red in |- *; intros.
        elim n; apply (C_ina_inv2 _ _ co _ _ H9).

        elim n; apply (C_ina_inv1 _ _ co _ _ H9).

        rewrite e; rewrite H8.
        apply E_set_disjoint; trivial.

        apply A_in_left; apply E_left.

        fold (Union Arc) A_union in |- *; rewrite H7; rewrite e; rewrite H8.
        trivial.

        apply A_in_left; apply E_left.

        trivial.

        case (V_union_single_dec _ _ _ n H0); intros.
        rewrite <- e in H2;
         generalize (C_pendant_isolated _ _ co x y y0 n H2); 
         intros.
        generalize (C_minus_isolated _ _ co y0 v2 H8); intros.
        decompose [and] H9.
        apply C_eq with (v := V_single y) (a := A_empty).
        symmetry  in |- *; apply (V_union_single_single v' y y0).
        red in |- *; intros Heq; elim n; rewrite Heq; trivial.

        trivial.

        rewrite H10 in H4; trivial.

        apply (A_union_edge_edge a0 a' x0 y0).
        trivial.

        trivial.

        trivial.

        rewrite <- H7.
        rewrite H10 in v1; inversion v1.
        rewrite e; apply A_union_eq.
        apply E_set_eq.

        trivial.

        apply C_isolated.

        apply
         C_eq
          with
            (v := V_union (V_single y) (V_inter v0 v'))
            (a := A_union (E_set x y) (A_inter a0 a')).
        apply (V_union_single_inter y y0).
        trivial.

        red in |- *; intros Heq; elim n; rewrite Heq; trivial.

        trivial.

        apply (A_union_single_inter x y x0 y0).
        red in |- *; intros; elim n; apply (C_ina_inv2 _ _ co _ _ H8).

        red in |- *; intros; elim n; apply (C_ina_inv1 _ _ co _ _ H8).

        apply E_set_diff2.
        red in |- *; intros Heq; elim n; rewrite Heq; trivial.

        red in |- *; intros Heq; elim n; rewrite Heq; trivial.

        trivial.

        apply C_leaf.
        apply (H x0 y0 v3 v2).
        intros; apply (H2 z).
        apply A_in_right; trivial.

        red in |- *; intros Hi; elim H3; inversion Hi; trivial.

        symmetry  in |- *; rewrite V_inter_commut;
         apply (V_union_single_inter y0 y).
        trivial.

        red in |- *; intros Heq; elim n; rewrite <- Heq; trivial.

        auto.

        unfold A_inter in |- *.
        rewrite (A_inter_commut a0 a'); apply A_not_inter; trivial.

        unfold A_inter in |- *.
        rewrite (A_inter_commut a0 a'); apply A_not_inter; trivial.

        rewrite A_inter_commut; symmetry  in |- *;
         apply (A_union_single_inter x0 y0 x y).
        trivial.

        trivial.

        apply E_set_diff4; red in |- *; intros Heq; elim n; rewrite Heq;
         trivial.

        auto.

        apply V_in_inter.
        trivial.

        case (V_union_single_dec y0 x v'); intros.
        trivial.

        rewrite <- H4; apply V_in_right; trivial.

        elim n; rewrite (H2 y).
        trivial.

        rewrite e; apply A_in_left; apply E_right.

        trivial.

        red in |- *; intros Hi; elim n; inversion Hi; trivial.

        generalize
         (E_not_eq_traversal_pendant _ _ co x y x0 y0 v1 v2 n n0 n1 H0 H1 H2);
         intros.
        apply C_eq with (v := v') (a := A_union (E_set x y) (A_inter a0 a')).
        trivial.

        apply (A_union_single_inter x y x0 y0); trivial.

        apply C_edge.
        apply (H x0 y0 H0 H1).
        intros; apply H2; apply A_in_right; trivial.

        trivial.

        trivial.

        unfold A_inter in |- *.
        rewrite (A_inter_commut a0 a'); apply A_not_inter; trivial.

        unfold A_inter in |- *.
        rewrite (A_inter_commut a0 a'); apply A_not_inter; trivial.

        rewrite A_inter_commut; symmetry  in |- *;
         apply (A_union_single_inter x0 y0 x y); auto.

        rewrite H4 in v1; inversion v1.
        elim H8; inversion H9.
        rewrite <- (H2 y).
        apply E_set_eq.

        rewrite H11; apply A_in_left; apply E_right.

        trivial.

        rewrite H4 in v2; inversion v2.
        elim H8; inversion H9.
        rewrite <- (H2 x).
        trivial.

        rewrite H11; apply A_in_left; apply E_left.

        trivial.

        trivial.

        apply A_not_inter; trivial.

        apply A_not_inter; trivial.

        apply (H x y).
        rewrite e; trivial.

        rewrite e; trivial.

        rewrite e0; trivial.

        trivial.

        rewrite e; trivial.

        trivial.

        trivial.

        rewrite e0; trivial.
Qed.

End INVERSION_CONNECTED.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
