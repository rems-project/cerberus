Add LoadPath "../../../../theory/metatheory_8.3".
Require Import Metatheory.

Section MoreDom.

Variable X: Type.

Lemma in_dom_cons_inv : forall a (v:X) l id0,
  id0 `in` dom ((a,v)::l) ->
  id0 = a \/ id0 `in` dom l.
Proof.
  intros.
  simpl in H. fsetdec.
Qed.

Lemma in_dom_app_inv : forall id0 D1 D2,
  id0 `in` D1 `union` D2 ->
  id0 `in` D1 \/ id0 `in` D2.
Proof.
  intros.
  fsetdec.
Qed.

Lemma in_dom_ext_right : forall i0 D1 D2,
  i0 `in` D1 ->
  i0 `in` D1 `union` D2.
Proof. fsetdec. Qed.

Lemma in_dom_ext_left : forall i0 D1 D2,
  i0 `in` D1 ->
  i0 `in` D2 `union` D1.
Proof. fsetdec. Qed.

End MoreDom.

Section MoreAssocLists.

Variable X: Type.
Definition AssocList := list (atom*X).

(* update if exists, add it otherwise *)
Fixpoint updateAddAL (m:AssocList) (i:atom) (gv:X) : AssocList :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateAddAL m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint updateAL (m:AssocList) (i:atom) (gv:X) : AssocList :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (eq_dec i i')
  then (i', gv)::m'
  else (i', gv')::updateAL m' i gv
end.

Fixpoint lookupAL (m:AssocList) (i:atom) : option X :=
match m with
| nil => None
| (i', gv')::m' =>
  if (eq_dec i i')
  then Some gv'
  else lookupAL m' i
end.

Fixpoint deleteAL (m:AssocList) (i:atom) : AssocList :=
match m with
| nil => nil
| (id0, gv0)::m' => 
    if (i == id0) then deleteAL m' i else (id0, gv0)::deleteAL m' i
end.

Definition rollbackAL (locals : AssocList) (i:atom) (lc0 : AssocList) 
  : AssocList :=
match (lookupAL lc0 i) with
| Some gv0 => updateAL locals i gv0
| None => deleteAL locals i
end.

Lemma updateAddAL_mono : forall l1 id0 e0 id1,
  id1 `in` dom l1 ->
  id1 `in` dom (updateAddAL l1 id0 e0).
Proof.
  induction l1; intros; simpl in *.    
    contradict H; fsetdec.

    destruct a.
    destruct (id0 == a); subst; simpl; auto.
      assert (id1 = a \/ id1 `in` dom l1) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
Qed.        

Lemma lookupAL_updateAL_in : forall m id0 gv0,
  id0 `in` dom m ->
  lookupAL (updateAL m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    simpl in H. contradict H; auto.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); 
        subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
        subst; simpl; auto.
        contradict n; auto.

        assert (id0 = a \/ id0 `in` dom m) as J. simpl in H. fsetdec.
        destruct J as [J | J]; subst.
          contradict n; auto.
          apply IHm with (gv0:=gv0) in J; auto.
Qed.   

Lemma lookupAL_updateAddAL_eq : forall m id0 gv0,
  lookupAL (updateAddAL m id0 gv0) id0 = Some gv0.
Proof.
  induction m; intros; simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 id0); subst; 
      simpl; auto.
      contradict n; auto.  

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); 
        subst; simpl; auto.
        contradict n; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
        subst; simpl; auto.
        contradict n; auto.
Qed.   

Lemma notin_lookupAL_None : forall m id0,
  id0 `notin` dom m ->
  lookupAL m id0 = None.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
    simpl in H. 
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; simpl; auto.
      contradict H; auto.
Qed.

Lemma lookupAL_updateAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupAL m id1 = lookupAL (updateAL m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
        subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
          subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); 
              subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
              subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
              subst; simpl; auto.
              contradict n0; auto.
Qed.   

Lemma lookupAL_updateAddAL_neq : forall m id0 id1 gv0,
  id1 <> id0 ->
  lookupAL m id1 = lookupAL (updateAddAL m id0 gv0) id1.
Proof.
  induction m; intros; simpl; auto.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
      subst; auto.
      contradict H; auto.

    destruct a.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 id0); 
        subst; simpl; auto.
        contradict H; auto.
        destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
          subst; simpl; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            contradict H; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); 
              subst; simpl; auto.
              contradict n1; auto.
          destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
            subst; simpl; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
              subst; simpl; auto.
              contradict n; auto.
            destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); 
              subst; simpl; auto.
              contradict n0; auto.
Qed.   

Lemma lookupAL_Some_indom : forall m id0 gv,
  lookupAL m id0 = Some gv ->
  id0 `in` dom m.
Proof.
  induction m; intros.
    simpl in H. inversion H.

    simpl in H. destruct a. 
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; 
      simpl; auto.
      apply IHm in H; auto.
Qed.  

Lemma lookupAL_None_notindom : forall m id0,
  lookupAL m id0 = None ->
  id0 `notin` dom m.
Proof.
  induction m; intros.
    auto.

    simpl in H. destruct a. 
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; 
      simpl; auto.
      inversion H.
Qed.

Lemma lookupAL_updateAL_notin : forall m id1 id0 gv0,
  id0 `notin` dom m ->
  lookupAL (updateAL m id0 gv0) id1 = lookupAL m id1.
Proof.
  induction m; intros; simpl; auto.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; 
      simpl.
      simpl in H. contradict H; auto.

      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst;
        simpl; auto.
Qed.

Lemma lookupAL_deleteAL_eq : forall m id0,
  lookupAL (deleteAL m id0) id0 = None.
Proof.
  induction m; intros id0; simpl; auto.
  destruct a.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
    subst; auto.

    simpl.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; auto.
      congruence.
Qed.

Lemma indom_lookupAL_Some : forall m id0,
  id0 `in` dom m ->
  exists gv0, lookupAL m id0 = Some gv0.
Proof.
  induction m; intros.
    simpl in H.
    contradict H; auto.

    destruct a.
    simpl in H.
    assert (id0 = a \/ id0 `in` dom m) as J.
      fsetdec.
    destruct J as [EQ | J]; subst.
      simpl.
      exists x.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); auto.
        contradict n; auto.

      simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; 
        auto.
        exists x. auto.
Qed.

Lemma updateAL_dom_eq : forall m id0 gv0,
  dom m [=] dom (updateAL m id0 gv0).
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
      simpl. fsetdec.
      simpl. rewrite <- IHm; auto. fsetdec.
Qed.

Lemma updateAL_uniq : forall m id0 gv0,
  uniq m ->
  uniq (updateAL m id0 gv0).
Proof.
  intros m id0 gv0 Uniq.
  induction Uniq; simpl; auto.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; 
    auto.
    simpl_env.
    apply uniq_push; auto.
      rewrite <- updateAL_dom_eq; auto.
Qed.

Lemma lookupAL_deleteAL_neq : forall m id0 id1,
  id0 <> id1 ->
  lookupAL (deleteAL m id0) id1 = lookupAL m id1.
Proof.
  induction m; intros id0 id1 id0_isnt_id1; simpl; auto.
  destruct a.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; 
      auto.
      contradict id0_isnt_id1; auto.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; 
      simpl.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) a a); subst; 
        auto.
        contradict n0; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id1 a); subst; 
        auto.
        contradict n0; auto.
Qed.

Lemma deleteAL_dom_sub : forall m id0,
  dom (deleteAL m id0) [<=] dom m.
Proof.
  induction m; intros; simpl.
    fsetdec.

    destruct a.
    assert (J:=@IHm id0).
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); simpl; 
      subst; fsetdec.
Qed.

Lemma deleteAL_uniq : forall m id0,
  uniq m ->
  uniq (deleteAL m id0).
Proof.
  intros m id0 Uniq.
  induction Uniq; simpl; auto.
  destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 x); subst; 
    auto.
    simpl_env.
    assert (J:=@deleteAL_dom_sub E id0).
    apply uniq_push; auto.
Qed.

Lemma updateAddAL_dom_eq : forall sm id0 st0,
  dom (updateAddAL sm id0 st0) [=] dom sm `union` {{id0}}.
Proof.
  induction sm; intros; simpl; try solve [fsetdec].
    destruct a. 
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); simpl; 
      try solve [fsetdec].
      assert (J:=@IHsm id0 st0). fsetdec.
Qed.

Lemma updateAddAL_uniq : forall sm id0 st0,
  uniq sm ->
  uniq (updateAddAL sm id0 st0).
Proof.
  induction sm; intros; simpl; auto.
    destruct a.

    destruct_uniq.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; 
      try solve [solve_uniq].
      apply IHsm with (id0:=id0)(st0:=st0) in H. 
      assert (J:=@updateAddAL_dom_eq sm id0 st0).
      solve_uniq.
Qed.

Lemma updateAddAL_inversion : forall sm id0 st0 id1 st1,
  uniq sm ->
  binds id1 st1 (updateAddAL sm id0 st0) ->
  (id0 <> id1 /\ binds id1 st1 sm) \/ (id0 = id1 /\ st0 = st1).
Proof.
  induction sm; intros id0 st0 id1 st1 Uniq Binds; simpl in Binds.
    analyze_binds Binds.

    destruct a.
    inversion Uniq; subst.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.
      analyze_binds Binds.
      left. split; auto.
        apply binds_In in BindsTac.
        fsetdec.

      analyze_binds Binds.
      apply IHsm in BindsTac; auto.
        destruct BindsTac; auto.
          destruct H; auto.
Qed.

Lemma updateAddAL_in_inversion : forall sm id0 st0 id1,
  uniq sm ->
  id1 `in` dom (updateAddAL sm id0 st0) ->
  (id0 <> id1 /\ id1 `in` dom sm) \/ (id0 = id1).
Proof.
  induction sm; intros id0 st0 id1 Uniq Hin; simpl in Hin.
    right. fsetdec.

    destruct a.
    inversion Uniq; subst.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst.      
      destruct (@in_dom_cons_inv _ _ _ _ _ Hin) as [EQ | id1_in_sm]; subst; auto.
        left. split; fsetdec.

      destruct (@in_dom_cons_inv _ _ _ _ _ Hin) as [EQ | id1_in_sm]; subst; simpl; auto.
        apply IHsm in id1_in_sm; auto.
        destruct id1_in_sm as [[id0_isnt_id1 id1_in_sm] | EQ]; auto.
Qed.
            
Lemma binds_updateAddAL_eq : forall sm id0 st0,
  binds id0 st0 (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0; simpl; auto.
    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
Qed.

Lemma binds_updateAddAL_neq : forall sm id0 st0 id1 st1,
  binds id1 st1 sm ->
  id0 <> id1 ->
  binds id1 st1 (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0 id1 st1 Hbinds id0_neq_id1; simpl; auto.
    destruct a.
    simpl_env in Hbinds.
    analyze_binds Hbinds.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
        contradict id0_neq_id1; auto.

      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; auto.
Qed.

Lemma in_updateAddAL_eq : forall sm id0 st0,
  id0 `in` dom (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0; simpl; auto.
    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
Qed.

Lemma in_updateAddAL_neq : forall sm id0 st0 id1,
  id1 `in` dom sm ->
  id0 <> id1 ->
  id1 `in` dom (updateAddAL sm id0 st0).
Proof.
  induction sm; intros id0 st0 id1 Hbinds id0_neq_id1; simpl; auto.
    destruct a.
    apply in_dom_cons_inv in Hbinds.
    destruct Hbinds; subst.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); subst; simpl; auto.
Qed.

Lemma mergeALs_inv : forall l2b l2b' B l0,
  uniq (l2b++l2b') ->
  lookupAL (l2b++l2b') l0 = Some B ->
  lookupAL l2b l0 = Some B \/ 
  lookupAL l2b' l0 = Some B.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    inversion H; subst.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); subst; auto.
Qed.

Lemma mergeALs_app : forall l2b l2b' B l0,
  uniq (l2b++l2b') ->
  lookupAL l2b l0 = Some B \/ lookupAL l2b' l0 = Some B ->
  lookupAL (l2b++l2b') l0 = Some B.
Proof.
  intros.
  induction l2b; auto.
    destruct H0 as [H0 | H0]; simpl_env; auto.
    inversion H0.

    destruct a. simpl in H. 
    inversion H; subst. clear H.
    destruct H0 as [H0 | H0]; simpl in *.
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); 
        subst; auto.        
      destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); 
        subst; auto.
        apply lookupAL_Some_indom in H0.
        contradict H0; auto.
Qed.

Lemma lookupAL_updateAL_Some_eq : forall lc id0 gv0 gv1,
  lookupAL lc id0 = Some gv0 ->
  lookupAL (updateAL lc id0 gv1) id0 = Some gv1.
Proof.
  intros lc id0 gv0 gv1 Hl.
  destruct (AtomSetProperties.In_dec id0 (dom lc)).
    rewrite lookupAL_updateAL_in; auto.

    rewrite notin_lookupAL_None in Hl; auto.
    inversion Hl.
Qed.

Lemma lookupAL_updateAL_None_eq : forall lc id0 gv1,
  lookupAL lc id0 = None ->
  lookupAL (updateAL lc id0 gv1) id0 = None.
Proof.
  intros lc id0 gv1 Hl.
  destruct (AtomSetProperties.In_dec id0 (dom lc)).
    apply indom_lookupAL_Some in i.
    destruct i as [gv0 i].
    rewrite i in Hl. 
    inversion Hl.

    rewrite lookupAL_updateAL_notin; auto.
Qed.

Lemma lookupAL_updateAL_ident: forall id0 gv0 lc ,
  lookupAL lc id0 = Some gv0 ->
  updateAL lc id0 gv0 = lc.
Proof.
  induction lc; simpl; intros; auto.
    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; auto.
      inversion H. subst. auto.

      rewrite IHlc; auto.
Qed.

Lemma lookupAL_updateAddAL_ident: forall id0 gv0 lc ,
  lookupAL lc id0 = Some gv0 ->
  updateAddAL lc id0 gv0 = lc.
Proof.
  induction lc; simpl; intros; auto.
    congruence.

    destruct a.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) id0 a); 
      subst; auto.
      inversion H. subst. auto.

      rewrite IHlc; auto.
Qed.

Lemma lookupAL_rollbackAL_neq : forall lc id0 lc0 id1,
  id0 <> id1 ->
  lookupAL lc id1 = lookupAL (rollbackAL lc id0 lc0) id1.
Proof.
  intros lc id0 lc0 id1 id0_isnt_id1.
  unfold rollbackAL.
  destruct (lookupAL lc0 id0).
    eapply lookupAL_updateAL_neq; eauto.
    rewrite lookupAL_deleteAL_neq; auto.
Qed.

Lemma lookupAL_rollbackAL_Some_eq : forall lc id0 lc0 gv0,
  lookupAL lc id0 = Some gv0 ->
  lookupAL (rollbackAL lc id0 lc0) id0 = lookupAL lc0 id0.
Proof.
  intros lc id0 lc0 gv0 HlookupAL.
  unfold rollbackAL.
  remember (lookupAL lc0 id0) as ogv0.
  destruct ogv0.
    rewrite Heqogv0.
    erewrite lookupAL_updateAL_Some_eq with (gv0:=gv0); eauto.

    rewrite lookupAL_deleteAL_eq; auto.
Qed.

Lemma lookupAL_rollbackAL_None_eq : forall lc id0 lc0,
  lookupAL lc id0 = None ->
  lookupAL (rollbackAL lc id0 lc0) id0 = None.
Proof.
  intros lc id0 lc0 HlookupAL.
  unfold rollbackAL.
  destruct (lookupAL lc0 id0).
    erewrite lookupAL_updateAL_None_eq; eauto.
    erewrite lookupAL_deleteAL_eq; eauto.
Qed.

Lemma rollbackAL_uniq : forall id0 lc0 lc,
  uniq lc ->
  uniq (rollbackAL lc id0 lc0).
Proof.
  intros id0 lc0 lc Huniqc.
  unfold rollbackAL.
  destruct (lookupAL lc0 id0).
    apply updateAL_uniq; auto.
    apply deleteAL_uniq; auto.
Qed.

Lemma lookupAL_rollbackAL_eq : forall lc id0 lc0 gv,
  lookupAL lc id0 = Some gv ->
  lookupAL (rollbackAL lc id0 lc0) id0 = lookupAL lc0 id0.
Proof.
  intros lc id0 lc0 gv HlookupAL.
  unfold rollbackAL.
  remember (lookupAL lc0 id0) as ogv0.
  destruct ogv0.
    apply lookupAL_Some_indom in HlookupAL.
    rewrite lookupAL_updateAL_in; auto.

    rewrite lookupAL_deleteAL_eq; auto.
Qed.

Definition eqAL lc1 lc2 := 
  forall i, lookupAL lc1 i = lookupAL lc2 i.

Lemma eqAL_refl : forall lc,
  eqAL lc lc.
Proof. unfold eqAL. auto. Qed.

Lemma eqAL_sym : forall lc1 lc2,
  eqAL lc1 lc2 ->
  eqAL lc2 lc1.
Proof. unfold eqAL. auto. Qed.

Lemma eqAL_trans : forall lc1 lc2 lc3,
  eqAL lc1 lc2 ->
  eqAL lc2 lc3 ->
  eqAL lc1 lc3.
Proof. 
  unfold eqAL. 
  intros.
  assert (J1:=@H i).
  assert (J2:=@H0 i).
  rewrite J1. auto.
Qed.

Lemma eqAL_indom_iff : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  (id0 `in` dom lc1 <-> id0 `in` dom lc1').
Proof.
  intros lc1 lc1' id0 HeqAL.
  split; intro J.
    assert (J':=@HeqAL id0).
    apply indom_lookupAL_Some in J; auto.
    destruct J as [gv0 J].
    rewrite J' in J.
    apply lookupAL_Some_indom in J; auto.
   
    assert (J':=@HeqAL id0).
    apply indom_lookupAL_Some in J; auto.
    destruct J as [gv0 J].
    rewrite J in J'.
    apply lookupAL_Some_indom in J'; auto.
Qed.

Lemma eqAL_indom_onlyif : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  id0 `in` dom lc1 ->
  id0 `in` dom lc1'.
Proof.
  intros.
  apply eqAL_indom_iff with (id0:=id0) in H.
  destruct H; auto.
Qed.

Lemma eqAL_indom_if : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  id0 `in` dom lc1' ->
  id0 `in` dom lc1.
Proof.
  intros.
  apply eqAL_indom_iff with (id0:=id0) in H.
  destruct H; auto.
Qed.

Lemma eqAL_notindom_iff : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  (id0 `notin` dom lc1 <-> id0 `notin` dom lc1').
Proof.
  intros.
  split; intro J.
    apply notin_lookupAL_None in J.
    rewrite H in J.
    apply lookupAL_None_notindom in J; auto.

    apply notin_lookupAL_None in J.
    rewrite <- H in J.
    apply lookupAL_None_notindom in J; auto.
Qed.

Lemma eqAL_notindom_onlyif : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  id0 `notin` dom lc1 -> 
  id0 `notin` dom lc1'.
Proof.
  intros.
  apply eqAL_notindom_iff with (id0:=id0) in H.
  destruct H; auto.
Qed.

Lemma eqAL_notindom_if : forall lc1 lc1' id0,
  eqAL lc1 lc1' ->  
  id0 `notin` dom lc1' ->
  id0 `notin` dom lc1.
Proof.
  intros.
  apply eqAL_notindom_iff with (id0:=id0) in H.
  destruct H; auto.
Qed.

Lemma eqAL_updateAL : forall lc1 lc2 id0 gv0,
  eqAL lc1 lc2 ->
  eqAL (updateAL lc1 id0 gv0) (updateAL lc2 id0 gv0).
Proof.
  unfold eqAL. 
  intros.
  assert (J:=H i) .
  destruct (id0==i); subst.
    destruct (@AtomSetProperties.In_dec i (dom lc1)) 
      as [id0_in_lc1 | id0_notin_lc1].
      rewrite lookupAL_updateAL_in; auto.
      rewrite lookupAL_updateAL_in; auto.
      eapply eqAL_indom_onlyif; eauto.

      rewrite lookupAL_updateAL_notin; auto.
      rewrite lookupAL_updateAL_notin; auto.
      eapply eqAL_notindom_onlyif; eauto.

    rewrite <- lookupAL_updateAL_neq; auto.
    rewrite <- lookupAL_updateAL_neq; auto.
Qed.

Lemma eqAL_updateAddAL : forall lc1 lc2 id0 gv0,
  eqAL lc1 lc2 ->
  eqAL (updateAddAL lc1 id0 gv0) (updateAddAL lc2 id0 gv0).
Proof.
  unfold eqAL. 
  intros.
  assert (J:=H i) .
  destruct (id0==i); subst.
    rewrite lookupAL_updateAddAL_eq; auto.
    rewrite lookupAL_updateAddAL_eq; auto.

    erewrite <- lookupAL_updateAddAL_neq; eauto.
    erewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

End MoreAssocLists.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

