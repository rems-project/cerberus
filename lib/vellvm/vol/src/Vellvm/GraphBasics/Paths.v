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



(* Different definitions of pathes in a graph, directed or not.         *)

(* The following notions are defined :                                  *)
(*      - Walk : defined by 2 ends,                                     *)
(*                      a list of vertices and a list of edges          *)
(*              constructors : W_null, W_step;                          *)
(*      - Trail : walk without repetition of edge,                      *)
(*              constructors : T_null, T_step;                          *)
(*      - Path : trail without repetition of inner vertex,              *)
(*              constructors : P_null, P_step;                          *)
(*      - Closed_walk, Closed_trail, Cycle.                             *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Graphs.
Require Export Degrees.

Section PATH.

Variable v : V_set.
Variable a : A_set.

Inductive Walk : Vertex -> Vertex -> V_list -> E_list -> Set :=
  | W_null : forall x : Vertex, v x -> Walk x x V_nil E_nil
  | W_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Walk y z vl el ->
      v x -> a (A_ends x y) -> Walk x z (y :: vl) (E_ends x y :: el).

Definition Closed_walk (x y : Vertex) (vl : V_list) 
  (el : E_list) (w : Walk x y vl el) := x = y.

Inductive Trail : Vertex -> Vertex -> V_list -> E_list -> Set :=
  | T_null : forall x : Vertex, v x -> Trail x x V_nil E_nil
  | T_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Trail y z vl el ->
      v x ->
      a (A_ends x y) ->
      (forall u : Edge, In u el -> ~ E_eq u (E_ends x y)) ->
      Trail x z (y :: vl) (E_ends x y :: el).

Definition Closed_trail (x y : Vertex) (vl : V_list) 
  (el : E_list) (t : Trail x y vl el) := x = y.

Inductive Path : Vertex -> Vertex -> V_list -> E_list -> Set :=
  | P_null : forall x : Vertex, v x -> Path x x V_nil E_nil
  | P_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Path y z vl el ->
      v x ->
      a (A_ends x y) ->
      x <> y ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      (forall u : Edge, In u el -> ~ E_eq u (E_ends x y)) ->
      Path x z (y :: vl) (E_ends x y :: el).

Definition Cycle (x y : Vertex) (vl : V_list) (el : E_list)
  (p : Path x y vl el) := x = y.

Lemma P_iny_vl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl el p; elim p; intros.
        absurd (V_nil = V_nil); auto.

        inversion p0.
        simpl in |- *; auto.

        rewrite H10; simpl in |- *; right.
        apply H; rewrite <- H10; discriminate.
Qed.

Lemma P_endx_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list), Path x y vl el -> v x.
Proof.
        intros x y vl el p; elim p; auto.
Qed.

Lemma P_endy_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list), Path x y vl el -> v y.
Proof.
        intros x y vl el p; elim p; auto.
Qed.

Lemma P_invl_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply (P_endx_inv _ _ _ _ p0).

        auto.
Qed.

Lemma P_inel_ina :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> a (A_ends x' y').
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        rewrite <- H3; rewrite <- H4; trivial.

        auto.
Qed.

Lemma P_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> In x' (x :: vl).
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        simpl in |- *; auto.

        simpl in |- *; right.
        apply (H x' y'); auto.
Qed.

Lemma P_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> In y' (x :: vl).
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        simpl in |- *; auto.

        simpl in |- *; right.
        apply (H x' y'); auto.
Qed.

Lemma P_backstep :
 forall (x y z : Vertex) (vl : V_list) (el : E_list),
 Path x z (y :: vl) el -> {el' : E_list &  Path y z vl el'}.
Proof.
        intros; inversion H.
        split with el0; trivial.
Qed.

Lemma Trail_isa_walk :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Trail x y vl el -> Walk x y vl el.
Proof.
        intros x y vl el t; elim t; intros.
        apply W_null; trivial.

        apply W_step; trivial.
Qed.

Lemma Path_isa_trail :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> Trail x y vl el.
Proof.
        intros x y vl el t; elim t; intros.
        apply T_null; trivial.

        apply T_step; trivial.
Qed.

End PATH.

Section EXTRACTED.

Variable v : V_set.
Variable a : A_set.

Fixpoint V_extract (x : Vertex) (vl : V_list) {struct vl} : V_list :=
  match vl with
  | nil => V_nil
  | y :: vl' =>
      if V_in_dec x vl' then V_extract x vl' else vl'
  end.

Lemma V_extract_spec: forall v1 v2 vl,
  In v1 (V_extract v2 vl) ->  v1 <> v2 ->
  In v1 vl.
Proof.
  induction vl; simpl; intros; auto.
    destruct (V_in_dec v2 vl); auto.
Qed.

Lemma V_extract_spec': forall v1 v2 vl,
  In v1 (V_extract v2 (v1::vl)) ->  v1 <> v2 ->
  In v1 vl.
Proof.
  induction vl; simpl; intros.
    destruct (V_in_dec v2 nil); auto.
    destruct (V_in_dec v2 (a0::vl)); auto.
Qed.

Lemma P_extract :
 forall (x y z : Vertex) (vl : V_list) (el : E_list),
 Path v a y z vl el ->
 In x (y :: vl) -> {el' : E_list &  Path v a x z (V_extract x (y :: vl)) el'}.
Proof.
        intros x y z vl; generalize y; elim vl; simpl in |- *; intros.
        split with el.
        replace x with y0; auto.
        case (V_in_dec y0 nil); auto.

        tauto.

        elim (P_backstep _ _ _ _ _ _ _ H0); intros.
        case (V_in_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl in |- *. intros. split with el. replace x with y0.
        trivial.
	
        tauto.
Qed.

Remark P_when_cycle :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el -> In x vl -> x = y.
Proof.
        intros x y vl el H; inversion H; intros.
        trivial.


        inversion H11.
        absurd (x = y0); auto.

        auto.
Qed.

Lemma Walk_to_path :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 {vl0 : V_list &  {el0 : E_list &  Path v a x y vl0 el0}}.
Proof.
        intros x y vl el w; elim w; intros.
        split with V_nil; split with E_nil; apply P_null; trivial.

        elim H; clear H; intros vl' H.
        elim H; clear H; intros el' H.
        case (V_in_dec x0 (y0 :: vl')); intros.
        elim (P_extract _ _ _ _ _ H i); intros.
        split with (V_extract x0 (y0 :: vl')); split with x1; auto.

        case (V_in_dec y0 vl'); intros.
        split with (y0 :: V_nil); split with (E_ends x0 y0 :: E_nil). apply P_step.
        replace z with y0.
        apply P_null; apply (P_endx_inv _ _ _ _ _ _ H).

        apply (P_when_cycle _ _ _ _ H); auto.

        trivial.

        trivial.

        red in |- *; intros; elim n; rewrite H0; simpl in |- *; auto.

        tauto.

	simpl in |- *. tauto.

        tauto.

        split with (y0 :: vl'); split with (E_ends x0 y0 :: el').
        apply P_step.
        trivial.

        trivial.

        trivial.

        red in |- *; intros; elim n; rewrite H0; simpl in |- *; auto.

        trivial.

        intros; absurd (In x0 vl').
        red in |- *; intros; elim n; simpl in |- *; auto.

        trivial.

        red in |- *; intros.
        elim n; inversion H1.
        apply (P_inxyel_inxvl _ _ _ _ _ _ H x0 y0).
        rewrite <- H3; auto.

        apply (P_inxyel_inyvl _ _ _ _ _ _ H y0 x0).
        rewrite <- H4; rewrite <- H5; rewrite H2; trivial.
Qed.

End EXTRACTED.

Section PATH_AND_DEGREE.

Variable v : V_set.
Variable a : A_set.
Variable g : Graph v a.

Lemma Path_degree_one :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el -> forall z : Vertex, In z vl -> degree z v a g > 0.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply Degree_not_isolated.
        split with x0; apply (G_non_directed v a g); trivial.

        apply H; auto.
Qed.

Lemma Path_consx_degree_one :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 vl <> V_nil -> forall z : Vertex, In z (x :: vl) -> degree z v a g > 0.
Proof.
        simple destruct vl; intros.
        absurd (nil = V_nil); auto.

        inversion H1.
        rewrite <- H2; apply Degree_not_isolated.
        inversion H; split with v0; trivial.

        apply (Path_degree_one x y (v0 :: l) el H); auto.
Qed.

Lemma Path_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 forall z : Vertex, In z vl -> z <> y -> degree z v a g > 1.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion p0.
        absurd (z0 = z).
        trivial.

        rewrite <- H2; auto.

        rewrite <- H2; apply Degree_not_pendant.
        split with x0.
        apply (G_non_directed v a g); trivial.

        split with y1.
        trivial.

        red in |- *; intros.
        elim (n1 (E_ends y0 y1)).
        rewrite <- H13; simpl in |- *; auto.

        rewrite H14; apply E_rev.

        apply H; trivial.
Qed.

Lemma Path_last_step :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 el <> E_nil -> exists z : Vertex, In (E_ends z y) el.
Proof.
        intros x y vl el p; elim p.
        intros; elim H; trivial.

        simple destruct el0; intros.
        split with x0.
        inversion p0.
        simpl in |- *; left; trivial.

        elim H; intros.
        split with x1.
        simpl in |- *; auto.

        discriminate.
Qed.

Lemma Cycle_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p -> forall z : Vertex, In z vl -> degree z v a g > 1.
Proof.
        intros; case (V_eq_dec z y); intros.
        rewrite e; apply Degree_not_pendant.
        inversion p.
        rewrite <- H4 in H0; inversion H0.

        inversion H.
        split with y0.
        rewrite <- H12; trivial.

        elim (Path_last_step y0 y vl0 el0 H1); intros.
        split with x1.
        apply (G_non_directed v a g); apply (P_inel_ina v a y0 y vl0 el0 H1);
         trivial.

        red in |- *; intros; elim (H7 (E_ends x1 y)).
        trivial.

        rewrite H12; rewrite H14; apply E_rev.

        inversion H1.
        absurd (x = y0).
        trivial.

        rewrite H15; trivial.

        discriminate.

        apply (Path_degree_two x y vl el p); trivial.
Qed.

Lemma Cycle_consx_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 vl <> V_nil ->
 Cycle v a x y vl el p ->
 forall z : Vertex, In z (x :: vl) -> degree z v a g > 1.
Proof.
        intros; inversion H1.
        rewrite <- H2; inversion H0.
        apply (Cycle_degree_two x y vl el p H0 y).
        apply (P_iny_vl v a x y vl el p); trivial.

        apply (Cycle_degree_two x y vl el p H0); trivial.
Qed.

Lemma Path_degree_zero_nil :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 (exists2 z : Vertex, In z (x :: vl) & degree z v a g = 0) -> vl = V_nil.
Proof.
        simple destruct vl; intros.
        trivial.

        elim H0; intros.
        absurd (degree x0 v a g > 0).
        omega.

        apply (Path_consx_degree_one _ _ _ _ H).
        discriminate.

        trivial.
Qed.

Lemma Cycle_degree_one_nil :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p ->
 (exists2 z : Vertex, In z (x :: vl) & degree z v a g <= 1) -> vl = V_nil.
Proof.
        simple destruct vl; intros.
        trivial.

        elim H0; intros.
        absurd (degree x0 v a g > 1).
        omega.

        apply (Cycle_consx_degree_two _ _ _ _ p).
        discriminate.

        trivial.

        trivial.
Qed.

End PATH_AND_DEGREE.

Section PATH_EQ.

Lemma Walk_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Walk v a x y vl el -> v = v' -> a = a' -> Walk v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply W_null.
        rewrite <- H0; trivial.

        apply W_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.
Qed.

Lemma Trail_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Trail v a x y vl el -> v = v' -> a = a' -> Trail v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply T_null.
        rewrite <- H0; trivial.

        intros; apply T_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.
Qed.

Lemma Path_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el -> v = v' -> a = a' -> Path v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply P_null.
        rewrite <- H0; trivial.

        intros; apply P_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End PATH_EQ.

Section PATH_IN_A_SUBGRAPH.

Lemma Walk_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 V_included v v' -> A_included a a' -> Walk v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply W_null; apply (H0 x0); trivial.

        apply W_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.
Qed.

Lemma Trail_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Trail v a x y vl el ->
 V_included v v' -> A_included a a' -> Trail v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply T_null; apply (H0 x0); trivial.

        apply T_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.

        trivial.
Qed.

Lemma Path_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 V_included v v' -> A_included a a' -> Path v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply P_null; apply (H0 x0); trivial.

        apply P_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_vertex :
 forall (v v' : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 v' x -> (forall z : Vertex, In z vl -> v' z) -> Path v' a x y vl el.
Proof.
        intros v v' a x y vl el p; elim p; intros.
        apply P_null; trivial.

        apply P_step.
        apply H.
        apply H1; simpl in |- *; auto.

        intros; apply H1; simpl in |- *; auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_cons_vertex :
 forall (v : V_set) (a : A_set) (x y z : Vertex) (vl : V_list) (el : E_list),
 Path (V_union (V_single z) v) a x y vl el ->
 z <> x -> ~ In z vl -> Path v a x y vl el.
Proof.
        intros v a x y z vl el p; elim p; intros.
        apply P_null.
        inversion v0.
        inversion H1; absurd (z = x0); auto.

        trivial.

        apply P_step.
        apply H.
        red in |- *; intros; elim H1.
        rewrite H2; simpl in |- *; auto.

        red in |- *; intros; elim H1; simpl in |- *; auto.

        inversion v0.
        inversion H2; absurd (z = x0); auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_arc :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 Graph v' a' ->
 v' x ->
 (forall x' y' : Vertex, In (E_ends x' y') el -> a' (A_ends x' y')) ->
 Path v' a' x y vl el.
Proof.
        intros v v' a a' x y vl el p; elim p; intros.
        apply P_null; trivial.

        apply P_step.
        apply H.
        trivial.

        apply (G_ina_inv2 v' a' H0 x0 y0).
        apply H2; simpl in |- *; auto.

        intros; apply H2; simpl in |- *; auto.

        trivial.

        apply H2; simpl in |- *; auto.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_cons_arc :
 forall (v : V_set) (a : A_set) (x y x' y' : Vertex) 
   (vl : V_list) (el : E_list),
 Path v (A_union (E_set x' y') a) x y vl el ->
 ~ In (E_ends x' y') el -> ~ In (E_ends y' x') el -> Path v a x y vl el.
Proof.
        intros v a x y x' y' vl el p; elim p; intros.
        apply P_null; trivial.

        apply P_step.
        apply H.
        red in |- *; intros; elim H0.
        simpl in |- *; auto.

        red in |- *; intros; elim H1; simpl in |- *; auto.

        trivial.

        inversion a0.
        inversion H2.
        absurd (In (E_ends x' y') (E_ends x0 y0 :: el0)).
        trivial.

        rewrite H5; rewrite H6; simpl in |- *; auto.

        absurd (In (E_ends y' x') (E_ends x0 y0 :: el0)).
        trivial.

        rewrite H5; rewrite H6; simpl in |- *; auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End PATH_IN_A_SUBGRAPH.

Section APPEND_WALKS.

Variable v : V_set.
Variable a : A_set.

Lemma Walk_append :
 forall (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
 Walk v a x y vl el ->
 Walk v a y z vl' el' -> Walk v a x z (vl ++ vl') (el ++ el').
Proof.
        intros x y z vl vl' el el' Hw; elim Hw; simpl in |- *; intros.
        trivial.

        apply W_step; auto.
Qed.

End APPEND_WALKS.

Section REVERSE_WALK.

Variable v : V_set.
Variable a : A_set.
Variable g : Graph v a.

Definition cdr (vl : V_list) : V_list :=
  match vl with
  | nil => V_nil
  | x :: vl' => vl'
  end.

Lemma cdr_app :
 forall vl vl' : V_list, vl <> V_nil -> cdr (vl ++ vl') = cdr vl ++ vl'.
Proof.
        simple induction vl; simpl in |- *; intros.
        absurd (V_nil = V_nil); auto.

        trivial.
Qed.

Fixpoint E_reverse (el : E_list) : E_list :=
  match el with
  | nil => E_nil
  | E_ends x y :: el' => E_reverse el' ++ E_ends y x :: E_nil
  end.

Lemma G_ends_in : forall x y : Vertex, a (A_ends x y) -> v x.
Proof.
        elim g; intros.
        inversion H.

        case (V_eq_dec x x0); intros.
        rewrite e; apply V_in_left; apply V_in_single.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H4; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

Lemma Walk_reverse :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> Walk v a y x (cdr (rev (x :: vl))) (E_reverse el).
Proof.
        intros; elim H; simpl in |- *; intros.
        apply W_null; trivial.

        rewrite cdr_app.
        apply (Walk_append v a z y0 x0).
        trivial.

        apply W_step.
        apply W_null; trivial.

        apply (G_ina_inv2 v a g x0 y0); trivial.

        apply (G_non_directed v a g); trivial.

        case (rev vl0); intros; simpl in |- *; discriminate.
Qed.

End REVERSE_WALK.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-R" "." "GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
