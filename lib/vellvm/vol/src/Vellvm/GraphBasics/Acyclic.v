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


(* An acyclic graph is indictively defined upon a set of vertices       *)
(*      and a set of arcs.                                              *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Paths.

Section ACYCLIC.

Inductive Acyclic : V_set -> A_set -> Set :=
  | AC_empty : Acyclic V_empty A_empty
  | AC_vertex :
      forall (v : V_set) (a : A_set) (ac : Acyclic v a) (x : Vertex),
      ~ v x -> Acyclic (V_union (V_single x) v) a
  | AC_leaf :
      forall (v : V_set) (a : A_set) (ac : Acyclic v a) (x y : Vertex),
      v x ->
      ~ v y -> Acyclic (V_union (V_single y) v) (A_union (E_set x y) a)
  | AC_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Acyclic v a -> Acyclic v' a'.

Lemma Acyclic_Isa_Graph :
 forall (v : V_set) (a : A_set), Acyclic v a -> Graph v a.
Proof.
        intros a v ac; elim ac; intros.
        apply G_empty.

        apply G_vertex; trivial.

        apply G_edge.
        apply G_vertex; trivial.

        apply V_in_right; trivial.

        apply V_in_left; apply V_in_single.

        red in |- *; intros Heq; elim n; rewrite <- Heq; trivial.

        red in |- *; intros; elim n; apply (G_ina_inv2 v0 a0 H x y); trivial.

        red in |- *; intros; elim n; apply (G_ina_inv1 v0 a0 H y x); trivial.

        apply G_eq with (v := v0) (a := a0); trivial.
Defined.

Lemma AC_ina_inv1 :
 forall (v : V_set) (a : A_set) (x y : Vertex),
 Acyclic v a -> a (A_ends x y) -> v x.
Proof.
        intros v a x y ac H;
         apply (G_ina_inv1 v a (Acyclic_Isa_Graph v a ac) x y); 
         trivial.
Qed.

Lemma AC_ina_inv2 :
 forall (v : V_set) (a : A_set) (x y : Vertex),
 Acyclic v a -> a (A_ends x y) -> v y.
Proof.
        intros v a x y ac H;
         apply (G_ina_inv2 v a (Acyclic_Isa_Graph v a ac) x y); 
         trivial.
Qed.

End ACYCLIC.

Section ACYCLIC_AND_DEGREES.

Remark AC_vertex_isolated :
 forall (v : V_set) (a : A_set) (x : Vertex),
 Acyclic v a ->
 ~ v x ->
 Acyclic (V_union (V_single x) v) a -> forall y : Vertex, ~ a (A_ends x y).
Proof.
        intros; red in |- *; intros.
        elim H0; apply (AC_ina_inv1 v a x y); trivial.
Qed.

Lemma AC_vertex_degree_zero :
 forall (v : V_set) (a : A_set) (ac : Acyclic v a) (x : Vertex) (Hn : ~ v x),
 degree x (V_union (V_single x) v) a
   (Acyclic_Isa_Graph (V_union (V_single x) v) a (AC_vertex v a ac x Hn)) = 0.
Proof.
        intros; apply Degree_isolated; unfold isolated in |- *.
        red in |- *; intros; elim Hn.
        apply AC_ina_inv1 with (a := a) (y := y); trivial.
Qed.

Remark AC_edge_pendant :
 forall (v : V_set) (a : A_set) (x y : Vertex),
 Acyclic v a ->
 v x ->
 ~ v y ->
 Acyclic (V_union (V_single y) v) (A_union (E_set x y) a) ->
 forall z : Vertex, A_union (E_set x y) a (A_ends z y) -> z = x.
Proof.
        intros; inversion H3.
        inversion H4; trivial.

        absurd (v y).
        trivial.

        apply (AC_ina_inv2 v a z y); trivial.
Qed.

Lemma AC_edge_degree_one :
 forall (v : V_set) (a : A_set) (ac : Acyclic v a) 
   (x y : Vertex) (Hp : v x) (Hn : ~ v y),
 degree y (V_union (V_single y) v) (A_union (E_set x y) a)
   (Acyclic_Isa_Graph (V_union (V_single y) v) (A_union (E_set x y) a)
      (AC_leaf v a ac x y Hp Hn)) = 1.
Proof.
        intros; apply Degree_pendant; unfold pendant in |- *.
        split with x.
        apply A_in_left; apply E_left.

        intros; inversion H.
        inversion H0; trivial.

        absurd (v y).
        trivial.

        apply AC_ina_inv1 with (a := a) (y := z); trivial.
Qed.

Remark one_le_one : forall n : nat, n = 1 -> n <= 1.
Proof.
        intros; omega.
Qed.

Lemma Acyclic_no_cycle :
 forall (v : V_set) (a : A_set) (Ac : Acyclic v a) 
   (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p -> vl = V_nil.
Proof.
        intros v a Ac; elim Ac; intros.
        inversion p.
        trivial.

        inversion H2.

        case (V_in_dec x (x0 :: vl)); intros.
        apply
         (Path_degree_zero_nil (V_union (V_single x) v0) a0
            (Acyclic_Isa_Graph (V_union (V_single x) v0) a0
               (AC_vertex v0 a0 ac x n)) x0 y vl el p).
        split with x.
        trivial.

        apply AC_vertex_degree_zero.

        cut (Path v0 a0 x0 y vl el); intros.
        apply (H _ _ _ _ H1); intros.
        apply H0.

        apply Path_supergraph_cons_vertex with (z := x).
        trivial.

        red in |- *; intros; elim n0; simpl in |- *; auto.

        red in |- *; intros; elim n0; simpl in |- *; auto.

        case (V_in_dec y (x0 :: vl)); intros.
        apply
         (Cycle_degree_one_nil (V_union (V_single y) v0)
            (A_union (E_set x y) a0)
            (Acyclic_Isa_Graph (V_union (V_single y) v0)
               (A_union (E_set x y) a0) (AC_leaf v0 a0 ac x y v1 n)) x0 y0 vl
            el p H0).
        split with y.
        trivial.

        apply one_le_one.
        apply AC_edge_degree_one.

        cut (Path v0 a0 x0 y0 vl el); intros.
        apply (H _ _ _ _ H1).
        apply H0.

        apply Path_supergraph_cons_arc with (x' := x) (y' := y).
        apply Path_supergraph_cons_vertex with (z := y).
        trivial.

        red in |- *; intros; elim n0; simpl in |- *; auto.

        red in |- *; intros; elim n0; simpl in |- *; auto.

        red in |- *; intros; elim n0;
         apply (P_inxyel_inyvl _ _ _ _ _ _ p x y); 
         trivial.

        red in |- *; intros; elim n0;
         apply (P_inxyel_inxvl _ _ _ _ _ _ p y x); 
         trivial.

        generalize H; rewrite e; rewrite e0; intros.
        apply (H1 _ _ _ _ p H0).
Qed.

End ACYCLIC_AND_DEGREES.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
