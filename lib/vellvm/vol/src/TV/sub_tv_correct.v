Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import ZArith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import sub_symexe.
Require Import alist.
Require Import infrastructure_props.
Require Import sub_tv_def.
Require Import sub_tv_dec.
Require Import sub_tv_infer.
Require Import sub_tv.
Require Import Coq.Bool.Sumbool.
Require Import symexe_tactic.

(* subAL *)

Definition subAL X fid lc1 lc2 := 
  forall i, i `in` dom lc1 -> 
    lookupAL X lc1 i = lookupAL X lc2 (rename_id fid i).

Lemma lookupAL_app1 : forall X (lc1:list (atom*X)) lc2 i,
  i `in` dom lc1 ->
  lookupAL X lc1 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_in_lc1.
    fsetdec.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); auto.
      apply IHlc1. fsetdec.
Qed.    

Lemma lookupAL_app2 : forall X lc1 (lc2:list (atom*X)) i,
  i `notin` dom lc1 ->
  lookupAL X lc2 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_notin_lc1; auto.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst; eauto.
      fsetdec.
Qed.    

Lemma subAL_app1 : forall X (lc1:list (atom*X)) lc2 lc fid,
  subAL _ fid lc1 lc ->
  subAL _ fid lc2 lc ->
  subAL _ fid (lc1 ++ lc2) lc.
Proof.
  intros X lc1 lc2 lc fid Hlc1_sub_lc Hlc2_sub_lc.
  intros i i_in_lc12.
  simpl_env in i_in_lc12.
  apply in_dom_app_inv in i_in_lc12.
  assert (i `in`  dom lc1 \/ i `notin` dom lc1) as i_in_lc1_dec. fsetdec.
  destruct i_in_lc1_dec as [i_in_lc1 | i_notin_lc1].
    rewrite <- Hlc1_sub_lc; auto.
    rewrite <- lookupAL_app1; auto.

    destruct i_in_lc12 as [i_in_lc1 | i_in_lc2].
      fsetdec.
      rewrite <- lookupAL_app2; auto.
Qed.

Lemma lookupALs_tail : forall X l2b l2b' l0,
  l0 `notin` dom l2b ->
  lookupAL X (l2b++l2b') l0 = lookupAL _ l2b' l0.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); subst; auto.
      fsetdec.
Qed.

Lemma subAL_app2 : forall X (lc1:list (atom*X)) lc2 lc fid,
  subAL _ fid lc1 lc ->
  disjoint lc1 lc2 ->
  ~ subAL _ fid lc2 lc ->
  ~ subAL _ fid (lc1 ++ lc2) lc.
Proof.
  intros X lc1 lc2 lc fid Hlc1_sub_lc Hdisj Hlc2_nsub_lc Hlc12_sub_lc.
  apply Hlc2_nsub_lc.
  intros i i_in_lc2.
    assert (i `notin` dom lc1) as i_notin_lc1. solve_uniq.
    assert (i `in` dom (lc1++lc2)) as i_in_lc12. simpl_env. fsetdec.
    apply Hlc12_sub_lc in i_in_lc12.
    erewrite lookupALs_tail in i_in_lc12; eauto.
Qed.
    
Definition smap_sub_prop Ps1 Ps2 fid sm1 sm2 := 
  forall i st1,
    lookupAL _ sm1 i = Some st1 ->
    exists st2, lookupAL _ sm2 (rename_id fid i) = Some st2 /\ 
      tv_sterm Ps1 Ps2 fid st1 st2 = true.

Definition sub_state fid (lc1 lc1':GVMap) (als1 als1':list mblock) f1 Mem1 Mem1'
  := 
  subAL _ fid lc1 lc1' /\ List.incl als1 als1' /\ 
  Memory.Mem.mem_inj f1 Mem1 Mem1'.
 
Definition phinodes_sub_prop fid (ps1 ps2:phinodes) :=
  forall i p1,
    lookupPhinode ps1 i = Some p1 ->
    exists p2, 
      lookupPhinode ps2 (rename_id fid i) = Some p2 /\ 
      tv_phinode fid p1 p2 = true.

Lemma NoDup_inv : forall A (l1 l2:list A),
  NoDup (l1++l2) -> NoDup l1 /\ NoDup l2.
Proof.
  induction l1; intros l2 Huniq. auto using NoDup_nil.
    inversion Huniq; subst.
    apply IHl1 in H2.
    destruct H2 as [H21 H22].
    split; auto.    
     apply NoDup_cons; auto.
       intro Ha_in_l1.
       apply H1.
         apply in_app_iff; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

