Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import alist.
Require Import infrastructure_props.
Require Import CoqListFacts.
Require Import symexe_def.

Export SimpleSE.

Definition sterm_dec_prop (st1:sterm) := forall st2, {st1=st2} + {~st1=st2}.
Definition list_sterm_dec_prop (sts1:list_sterm) := forall sts2, {sts1=sts2} + {~sts1=sts2}.
Definition list_sterm_l_dec_prop (stls1:list_sterm_l) := forall stls2, {stls1=stls2} + {~stls1=stls2}.
Definition smem_dec_prop (sm1:smem) := forall sm2, {sm1=sm2} + {~sm1=sm2}.
Definition sframe_dec_prop (sf1:sframe) := forall sf2, {sf1=sf2} + {~sf1=sf2}.

Lemma se_dec :
  (forall st1, sterm_dec_prop st1) *
  (forall sts1, list_sterm_dec_prop sts1) *
  (forall stls1, list_sterm_l_dec_prop stls1) *
  (forall sm1, smem_dec_prop sm1) *
  (forall sf1, sframe_dec_prop sf1).
Proof.
  (se_mut_cases (apply se_mutrec) Case); 
    unfold sterm_dec_prop, list_sterm_dec_prop, list_sterm_l_dec_prop, smem_dec_prop, sframe_dec_prop;
    intros.
  Case "sterm_val".
    destruct st2; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "sterm_bop".
    destruct st2; try solve [done_right].
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@Size.dec s s2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_fbop".
    destruct st2; try solve [done_right].
    destruct (@fbop_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_extractvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_insertvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_malloc".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "sterm_alloca".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "sterm_load".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [auto | done_right].
  Case "sterm_gep".    
    destruct st2; try solve [done_right].
    destruct (@bool_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@H0 l1); subst; try solve [auto | done_right].
  Case "sterm_trunc".
    destruct st2; try solve [done_right].
    destruct (@truncop_dec t t2); subst; try solve [done_right].
    destruct (@typ_dec t0 t3); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t1 t4); subst; try solve [auto | done_right].
  Case "sterm_ext".
    destruct st2; try solve [done_right].
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_cast".
    destruct st2; try solve [done_right].
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_icmp".
    destruct st2; try solve [done_right].
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_fcmp".
    destruct st2; try solve [done_right].
    destruct (@fcond_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_phi".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H l1); subst; try solve [auto | done_right].
  Case "sterm_select".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@H1 st2_3); subst; try solve [auto | done_right].
  Case "list_sterm_nil".
    destruct sts2; subst; try solve [auto | done_right].
  Case "list_sterm_cons".
    destruct sts2; subst; try solve [auto | done_right].
    destruct (@Size.dec s s1); subst; try solve [done_right].
    destruct (@H s2); subst; try solve [done_right].
    destruct (@H0 sts2); subst; try solve [auto | done_right].
  Case "list_sterm_l_nil".
    destruct stls2; subst; try solve [auto | done_right].
  Case "list_sterm_l_cons".
    destruct stls2; subst; try solve [auto | done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@l_dec l0 l2); subst; try solve [done_right].
    destruct (@H0 stls2); subst; try solve [auto | done_right].
  Case "smem_init".
    destruct sm2; subst; try solve [auto | done_right].
  Case "smem_malloc".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "smem_free".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_alloca".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "smem_load".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_store".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 s2); subst; try solve [auto | done_right].
    destruct (@H1 s3); subst; try solve [auto | done_right].
  Case "sframe_init".
    destruct sf2; subst; try solve [auto | done_right].
  Case "sframe_alloca".
    destruct sf2; subst; try solve [done_right].
    destruct (@H s2); subst; try solve [done_right].
    destruct (@H0 sf2); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H1 s3); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
Qed.

Lemma sterm_dec : forall (st1 st2:sterm), {st1=st2} + {~st1=st2}.
destruct se_dec as [[[[H _] _] _] _]. auto.
Qed.

Lemma list_sterm_dec :  forall (ts1 ts2:list_sterm), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[[_ H] _] _] _]. auto.
Qed. 

Lemma list_sterm_l_dec :  forall (ts1 ts2:list_sterm_l), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[_ H] _] _]. auto.
Qed. 

Lemma smem_dec : forall (sm1 sm2:smem), {sm1=sm2} + {~sm1=sm2}.
destruct se_dec as [[_ H] _]. auto.
Qed.

Lemma sframe_dec : forall (sf1 sf2:sframe), {sf1=sf2} + {~sf1=sf2}.
destruct se_dec as [_ H]. auto.
Qed.

Lemma sterminator_dec : forall (st1 st2:sterminator), {st1=st2} + {~st1=st2}.
Proof.
  decide equality.
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma list_typ_sterm_dec : forall (l1 l2:list (typ*sterm)), {l1=l2}+{~l1=l2}.
Proof.
  decide equality.
    destruct a. destruct p.
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma smap_dec : forall (sm1 sm2:smap), {sm1=sm2}+{~sm1=sm2}.
Proof.
  decide equality.
    destruct a. destruct p.
    destruct (@id_dec a a0); subst; try solve [done_right]. 
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma sterms_dec :  forall (ts1 ts2:list sterm), {ts1=ts2}+{~ts1=ts2}.
Proof.
  decide equality.
    destruct (@sterm_dec a s); subst; try solve [auto | done_right].
Qed.

Lemma sstate_dec : forall (sts1 sts2:sstate), {sts1=sts2} + {~sts1=sts2}.
Proof.
  decide equality.
    destruct (@sterms_dec SEffects0 SEffects1); subst; try solve [auto | done_right].
    destruct (@sframe_dec SFrame0 SFrame1); subst; try solve [auto | done_right].
    destruct (@smem_dec SMem0 SMem1); subst; try solve [auto | done_right].
    destruct (@smap_dec STerms0 STerms1); subst; try solve [auto | done_right].
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
