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



(* Different definitions of pathes in a directed graph.                 *)

(* The following notions are defined :                                  *)
(*      - D_walk : list of vertices joined one by one by arcs,          *)
(*                constructors : DW_null, DW_step;                      *)
(*      - D_trail : walk without repetition of arcs,                    *)
(*              constructors : DT_null, DT_step;                        *)
(*      - D_path : trail without repetition of inner vertices,          *)
(*              constructors : DP_null, DP_step;                        *)
(*      - D_closed_walk, D_closed_trail, D_cycle.                       *)

Add LoadPath "../../../../theory/metatheory_8.3".
Require Export Digraphs.

Section DIRECTED_PATHES.

Variable v : V_set.

Variable a : A_set.

Inductive D_walk : Vertex -> Vertex -> V_list -> A_list -> Prop :=
  | DW_null : forall x : Vertex, v x -> D_walk x x V_nil A_nil
  | DW_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_walk y z vl al ->
      v x -> a (A_ends x y) -> D_walk x z (y :: vl) (A_ends x y :: al).

Definition D_closed_walk :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_walk x x vl al.

Inductive D_trail : Vertex -> Vertex -> V_list -> A_list -> Prop :=
  | DT_null : forall x : Vertex, v x -> D_trail x x V_nil A_nil
  | DT_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_trail y z vl al ->
      v x ->
      a (A_ends x y) ->
      ~ In (A_ends x y) al -> D_trail x z (y :: vl) (A_ends x y :: al).

Definition D_closed_trail :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_trail x x vl al.

Inductive D_path : Vertex -> Vertex -> V_list -> A_list -> Prop :=
  | DP_null : forall x : Vertex, v x -> D_path x x V_nil A_nil
  | DP_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_path y z vl al ->
      v x ->
      a (A_ends x y) ->
      x <> y ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      ~ In (A_ends x y) al -> D_path x z (y :: vl) (A_ends x y :: al).

Definition D_cycle :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_path x x vl al.


Lemma D_trail_isa_walk :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (t : D_trail x y vl al),
 D_walk x y vl al.
Proof.
        intros x y vl al t; elim t; intros.
        apply DW_null; trivial.

        apply DW_step; trivial.
Qed.

Lemma D_path_isa_trail :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (p : D_path x y vl al),
 D_trail x y vl al.
Proof.
        intros x y vl al p; elim p; intros.
        apply DT_null; trivial.

        apply DT_step; trivial.
Qed.

Lemma D_path_isa_walk :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (p : D_path x y vl al),
 D_walk x y vl al.
Proof.
   intros. apply D_trail_isa_walk. apply D_path_isa_trail; auto.
Qed.

Lemma DW_iny_vl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl al d; elim d; intros.
        absurd (V_nil = V_nil); auto.

        inversion H.
        simpl in |- *; auto.

        rewrite H9; simpl in |- *; right.
        apply H0; rewrite <- H9; discriminate.
Qed.

Lemma DW_endx_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_walk x y vl al -> v x.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DW_endy_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_walk x y vl al -> v y.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DW_invl_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H3; subst; auto.
        apply (DW_endx_inv _ _ _ _ H).
Qed.

Lemma DW_inel_ina :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> a (A_ends x' y').
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H3; auto.
        inversion H4; subst; auto.
Qed.

Lemma DW_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In x' (x :: vl).
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H3.
          inversion H4.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DW_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In y' (x :: vl).
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H3.
          inversion H4.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DW_backstep :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk x z (y :: vl) al -> 
   exists al' : A_list, D_walk y z vl al' /\ (al = (A_ends x y) ::al').
Proof.
        intros; inversion H.
        split with al0. split; auto.
Qed.

Lemma DW_neq_ends_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), 
 D_walk x y vl al -> x <> y -> vl <> V_nil /\ al <> A_nil.
Proof.
        intros; inversion H; subst; auto.
          split; intro J; inversion J.
Qed.      

Lemma DW_Vnil_inv :
 forall (x y : Vertex) (al : A_list), 
 D_walk x y V_nil al -> x = y /\ al = A_nil.
Proof.
        intros; inversion H; subst; auto.
Qed.      

Lemma DW_Anil_inv :
 forall (x y : Vertex) (vl : V_list), 
 D_walk x y vl A_nil -> x = y /\ vl = V_nil.
Proof.
        intros; inversion H; subst; auto.
Qed.      

Lemma DP_iny_vl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl al d; elim d; intros.
        absurd (V_nil = V_nil); auto.

        inversion H.
          simpl in |- *; auto.

          rewrite H17; simpl in |- *; right.
          apply H0; rewrite <- H17; discriminate.
Qed.

Lemma DP_endx_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_path x y vl al -> v x.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DP_endy_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_path x y vl al -> v y.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DP_invl_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H7; subst; auto.
        apply (DP_endx_inv _ _ _ _ H).
Qed.

Lemma DP_inel_ina :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> a (A_ends x' y').
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H7; subst; auto.
        inversion H8; subst; auto.
Qed.

Lemma DP_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In x' (x :: vl).
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H7.
          inversion H8; subst.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DP_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In y' (x :: vl).
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H7.
          inversion H8; subst.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DP_endx_ninV :
 forall (x y : Vertex) (vl : V_list) (al : A_list), 
 D_path x y vl al -> x <> y -> ~ In x vl.
Proof.
  intros x y vl el d Hneq. inversion d; subst; simpl; auto.
  intro J. 
  destruct J as [J | J]; subst; auto.
Qed.

Lemma DP_backstep :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_path x z (y :: vl) al -> exists al' : A_list, D_path y z vl al'.
Proof.
        intros; inversion H.
        split with al0; trivial.
Qed.

End DIRECTED_PATHES.

Require Export Paths.

Section DEXTRACTED.

Variable v : V_set.
Variable a : A_set.

Lemma DW_extract :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al ->
 In x (y :: vl) -> 
 exists al' : A_list, D_walk v a x z (V_extract x (y :: vl)) al'.
Proof.
        intros x y z vl; generalize y; elim vl; simpl in |- *; intros.
        split with al.
        replace x with y0; auto.
        case (V_in_dec y0 nil); auto.

        tauto.

        elim (DW_backstep _ _ _ _ _ _ _ H0); intros.
        destruct H2 as [H2 Heq]; subst.
        case (V_in_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl in |- *. intros. 
        split with (A_ends y0 a0 :: x0). 
        replace x with y0.
          trivial.
	
          tauto.
Qed.

Lemma DW_cut :
 forall (y z: Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al -> vl <> V_nil ->
 forall x w,
 In x (y :: vl) -> 
 In w (y :: vl) -> 
 x <> y -> w <> y -> x <> w ->
    exists al1 : A_list, exists al2 : A_list, exists vl1 : V_list, 
    exists vl2 : V_list,
      (D_walk v a y x vl1 al1 /\ D_walk v a x z vl2 al2 /\
       (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl) /\ ~ In w (y::vl1)) \/
      (D_walk v a y w vl1 al1 /\ D_walk v a w z vl2 al2 /\
       (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl) /\ ~ In x (y::vl1)).
Proof.
  induction 1; simpl in *; intros.
    congruence.

    destruct H3 as [H3 | H3]; try congruence; subst.
    destruct H4 as [H4 | H4]; try congruence; subst.
    destruct vl.
      inversion H; subst.
      destruct H3 as [H3 | H3]; try solve [inversion H3]; subst.
      destruct H4 as [H4 | H4]; try solve [inversion H4]; subst.
      congruence.

      destruct (V_eq_dec y w); subst.
        exists (A_ends x w::nil). exists al. exists (w::nil). exists (v0::vl).
        right.
        split. constructor; auto. constructor; auto. apply DW_endx_inv in H; auto.
        split; auto. 
        split; auto. 
        split; auto. 
          intro J. 
          destruct J as [J | J]; subst.
            congruence.
            simpl in J. 
            destruct J as [J | J]; subst; auto.

      destruct (V_eq_dec y x0); subst.
        exists (A_ends x x0::nil). exists al. exists (x0::nil). exists (v0::vl).
        left.
        split. constructor; auto. constructor; auto. apply DW_endx_inv in H; auto.
        split; auto. 
        split; auto. 
        split; auto. 
          intro J. 
          destruct J as [J | J]; subst.
            congruence.
            simpl in J. 
            destruct J as [J | J]; subst; auto.

          eapply IHD_walk in H3; eauto.
            clear IHD_walk.
            destruct H3 as [al1 [al2 [vl1 [vl2 
              [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
              exists (A_ends x y::al1). exists al2. exists (y::vl1). exists vl2.
              right. rewrite <- J4.
              split. constructor; auto.
              split; auto. 
              split; auto. 
              split; auto. 
                intro J. 
                destruct J as [J | J]; subst.
                  congruence.
                  apply J5. simpl in J. auto.

              exists (A_ends x y::al1). exists al2. exists (y::vl1). exists vl2.
              left. rewrite <- J4.
              split. constructor; auto.
              split; auto. 
              split; auto. 
              split; auto. 
                intro J. 
                destruct J as [J | J]; subst.
                  congruence.
                  apply J5. simpl in J. auto.
            intro J. inversion J.          
Qed.

Lemma DW_split :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al ->
 In x (y :: vl) -> 
    exists al1 : A_list, exists al2 : A_list, exists vl1 : V_list, 
    exists vl2 : V_list,
      D_walk v a y x vl1 al1 /\ D_walk v a x z vl2 al2 /\
      (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl).
Proof.
  intros.
  induction H.
    assert (x0 = x) as EQ.
      simpl in H0. 
      destruct H0 as [H0 | H0]; inversion H0; auto.
    clear H0. subst.
    exists A_nil. exists A_nil. exists V_nil. exists V_nil.
    repeat split; try solve [auto | constructor; auto].

    destruct (V_eq_dec x x0); subst.
      exists A_nil. exists (A_ends x0 y :: al). exists V_nil. exists (y::vl). 
      repeat split; try solve [auto | constructor; auto].

      assert (In x (y::vl)) as Hin.
        simpl in H0. 
        destruct H0 as [H0 | H0]; auto; try congruence.
      clear H0. 
      apply IHD_walk in Hin.
      destruct Hin as [al1 [al2 [vl1 [vl2 [J1 [J2 [J3 J4]]]]]]]; subst.
      exists (A_ends x0 y::al1). exists al2. exists (y::vl1). exists vl2.
      repeat split; try solve [auto | constructor; auto].
Qed.

Lemma DP_extract :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_path v a y z vl al ->
 In x (y :: vl) -> 
 exists al' : A_list,  D_path v a x z (V_extract x (y :: vl)) al'.
Proof.
        intros x y z vl; generalize y; elim vl; simpl in |- *; intros.
        split with al.
        replace x with y0; auto.
        case (V_in_dec y0 nil); auto.

        tauto.

        elim (DP_backstep _ _ _ _ _ _ _ H0); intros.
        case (V_in_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl in |- *. intros. split with al. replace x with y0.
        trivial.
	
        tauto.
Qed.

Remark DP_when_cycle :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path v a x y vl al -> In x vl -> x = y.
Proof.
        intros x y vl al H; inversion H; intros.
        trivial.

        inversion H11.
        absurd (x = y0); auto.

        auto.
Qed.

Lemma DWalk_to_dpath :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk v a x y vl al ->
 exists vl0 : V_list, exists al0 : A_list, D_path v a x y vl0 al0.
Proof.
        intros x y vl al w; elim w; intros.
        split with V_nil; split with A_nil; apply DP_null; trivial.

        elim H0; clear H0; intros vl' H0.
        elim H0; clear H0; intros al' H0.
        case (V_in_dec x0 (y0 :: vl')); intros.
        elim (DP_extract _ _ _ _ _ H0 i); intros.
        split with (V_extract x0 (y0 :: vl')); split with x1; auto.

        case (V_in_dec y0 vl'); intros.
        split with (y0 :: V_nil); split with (A_ends x0 y0 :: A_nil). 
        apply DP_step.
        replace z with y0.
        apply DP_null; apply (DP_endx_inv _ _ _ _ _ _ H0).

        apply (DP_when_cycle _ _ _ _ H0); auto.

        trivial.

        trivial.

        red in |- *; intros; elim n; subst; simpl in |- *; auto.

        tauto.

	simpl in |- *. tauto.

        tauto.

        split with (y0 :: vl'); split with (A_ends x0 y0 :: al').
        apply DP_step.
        trivial.

        trivial.

        trivial.

        red in |- *; intros; elim n; subst; simpl in |- *; auto.

        trivial.

        intros; absurd (In x0 vl').
        red in |- *; intros; elim n; simpl in |- *; auto.

        trivial.

        red in |- *; intros.
        elim n; inversion w; apply (DP_inxyel_inxvl _ _ _ _ _ _ H0 x0 y0); auto.
Qed.

End DEXTRACTED.

Section DPATH_EQ.

Lemma DWalk_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (al : A_list),
 D_walk v a x y vl al -> v = v' -> a = a' -> D_walk v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DW_null.
        rewrite <- H0; trivial.

        apply DW_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.
Qed.

Lemma DTrail_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (al : A_list),
 D_trail v a x y vl al -> v = v' -> a = a' -> D_trail v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DT_null.
        rewrite <- H0; trivial.

        intros; apply DT_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.
Qed.

Lemma DPath_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (al : A_list),
 D_path v a x y vl al -> v = v' -> a = a' -> D_path v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DP_null.
        rewrite <- H0; trivial.

        intros; apply DP_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End DPATH_EQ.

Section APPEND_DWALKS.

Variable v : V_set.
Variable a : A_set.

Lemma DWalk_append :
 forall (x y z : Vertex) (vl vl' : V_list) (al al' : A_list),
 D_walk v a x y vl al ->
 D_walk v a y z vl' al' -> D_walk v a x z (vl ++ vl') (al ++ al').
Proof.
        intros x y z vl vl' al al' Hw; elim Hw; simpl in |- *; intros.
        trivial.

        apply DW_step; auto.
Qed.

End APPEND_DWALKS.

Lemma D_walk_iff: forall v1 a1 x y vl al v2 a2
  (H1: forall x, v2 x <-> v1 x) 
  (H2: forall x, a2 x <-> a1 x),
  D_walk v1 a1 x y vl al <->
  D_walk v2 a2 x y vl al.
Proof.
  intros.
  split; intro J.
    induction J; constructor; auto.
      apply H1; auto.
      apply H1; auto.
      apply H2; auto. 
    induction J; constructor; auto.
      apply H1; auto.
      apply H1; auto.
      apply H2; auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./" "-impredicative-set") ***
*** End: ***
 *)
