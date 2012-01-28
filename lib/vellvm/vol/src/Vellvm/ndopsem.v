Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
Require Import AST.
Require Import Floats.
Require Import Metatheory.
Require Import alist.
Require Import monad.
Require Import targetdata.
Require Import genericvalues.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import syntax.
Require Import typings.
Require Import typings_props.
Require Import opsem.
Require Import opsem_props.
Require Import opsem_wf.

Import LLVMsyntax.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.

Module MNDGVs.

Lemma singleton_inhabited : forall U (x:U), Inhabited U (Singleton U x).
Proof.
  intros. apply Inhabited_intro with (x:=x); auto using In_singleton.
Qed.

Lemma full_set_inhabited : forall U, 
  (exists x:U, True) -> Inhabited U (Full_set U).
Proof.
  intros. inversion H.
  apply Inhabited_intro with (x:=x); auto using Full_intro.
Qed.

Definition t := Ensemble GenericValue.
Definition instantiate_gvs (gv : GenericValue) (gvs : t) : Prop :=
  Ensembles.In _ gvs gv.
Definition inhabited (gvs : t) : Prop := Ensembles.Inhabited _ gvs.
Hint Unfold instantiate_gvs inhabited.
Definition cundef_gvs gv ty : t :=
match ty with
| typ_int sz => fun gv => exists z, gv = (Vint sz z, Mint (sz - 1))::nil
| typ_floatpoint fp_float => fun gv => exists f, gv = (Vfloat f, Mfloat32)::nil
| typ_floatpoint fp_double => fun gv => exists f, gv = (Vfloat f, Mfloat64)::nil
| typ_pointer _ => 
    fun gv => exists b, exists ofs, gv = (Vptr b ofs, AST.Mint 31)::nil
| _ => Singleton GenericValue gv
end.

Definition undef_gvs gv ty : t :=
match ty with
| typ_int sz =>
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists z, gv = (Vint sz z, Mint (sz-1))::nil)
| typ_floatpoint fp_float => 
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists f, gv = (Vfloat f, Mfloat32)::nil)
| typ_floatpoint fp_double => 
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists f, gv = (Vfloat f, Mfloat64)::nil)
| typ_pointer _ =>
    Ensembles.Union _ (Singleton _ gv)
      (fun gv => exists b, exists ofs, gv = (Vptr b ofs, AST.Mint 31)::nil)
| _ => Singleton GenericValue gv
end.

Definition cgv2gvs (gv:GenericValue) ty : t :=
match gv with
| (Vundef, _)::nil => cundef_gvs gv ty
| _ => Singleton _ gv
end.

Definition gv2gvs (gv:GenericValue) (ty:typ) : t :=
match gv with
| (Vundef, _)::nil => undef_gvs gv ty
| _ => Singleton GenericValue gv
end.

Notation "gv @ gvs" :=  
  (instantiate_gvs gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (gv2gvs gv t) (at level 41).

Lemma cundef_gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (cundef_gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct t; simpl in *;
    try solve [inv Heq1; inv Hin; erewrite int_typsize; eauto |
               inv Heq1; inv Hin; eauto].
    destruct f; try solve [inv Heq1; inv Hin; eauto].
    inv Heq1. inv Hin. inv H. simpl. auto.
Qed.

Lemma cundef_gvs__inhabited : forall gv ty, inhabited (cundef_gvs gv ty).
Proof.
  destruct ty; simpl; 
    try solve [eapply Ensembles.Inhabited_intro; constructor].
    eapply Ensembles.Inhabited_intro.
      exists (Int.zero s). auto.

    destruct f; try solve [
      eapply Ensembles.Inhabited_intro; exists Float.zero; auto |
      eapply Ensembles.Inhabited_intro; constructor].

    eapply Ensembles.Inhabited_intro.
      exists Mem.nullptr. exists (Int.repr 31 0). auto.
Qed.

Lemma undef_gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (undef_gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct t; simpl in *;
    try solve [inv Heq1; inv Hin; erewrite int_typsize; eauto |
               inv Heq1; inv Hin; eauto].

    inv Heq1; inv Hin; inv H; unfold Size.to_nat; 
      try solve [eauto | erewrite int_typsize; eauto].

    destruct f; try solve [inv Heq1; inv Hin; eauto |
                           inv Heq1; inv Hin; inv H; auto].

    inv Heq1; inv Hin; inv H; auto.
      inv H0. auto.
Qed.

Lemma undef_gvs__inhabited : forall gv ty, inhabited (undef_gvs gv ty).
Proof.
  destruct ty; simpl; try solve [
    eapply Ensembles.Inhabited_intro; apply Union_introl; constructor |
    eapply Ensembles.Inhabited_intro; constructor].

    destruct f; try solve [
      eapply Ensembles.Inhabited_intro; apply Union_introl; constructor |
      eapply Ensembles.Inhabited_intro; constructor].
Qed.

Lemma cgv2gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  gv' @ (cgv2gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv'.
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct gv; simpl in *.
    inv Hin. simpl. auto.

    destruct p.
    destruct v; try solve [inv Hin; simpl; auto].
    destruct gv; try solve [inv Hin; simpl; auto].
      eapply cundef_gvs__getTypeSizeInBits in Hin; eauto.
Qed.

Lemma cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, cundef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, cundef_gvs__inhabited.
Qed.

Lemma gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  forall gv', gv' @ (gv2gvs gv t) ->
  sizeGenericValue gv' = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8).
Proof.
  intros S los nts gv t sz al gv' Hwft Heq1 Heq2 Hin.
  destruct gv; simpl in *.
    inv Hin. simpl. auto.

    destruct p.
    destruct v; try solve [inv Hin; simpl; auto].
    destruct gv; try solve [inv Hin; simpl; auto].
      eapply undef_gvs__getTypeSizeInBits in Hin; eauto.
Qed.

Lemma gv2gvs__inhabited : forall gv t, inhabited ($ gv # t $).
Proof.
  intros gv t.
  destruct gv; simpl.
    apply Ensembles.Inhabited_intro with (x:=nil).
    apply Ensembles.In_singleton.

    destruct p.
    destruct v; auto using singleton_inhabited, undef_gvs__inhabited.
    destruct gv; auto using singleton_inhabited, undef_gvs__inhabited.
Qed.

Definition lift_op1 (f: GenericValue -> option GenericValue) gvs1 ty : option t 
  :=
  Some (fun gv2 => exists gv1, exists gv2', 
    gv1 @ gvs1 /\ f gv1 = Some gv2' /\ (gv2 @ $ gv2' # ty $)).

Definition lift_op2 (f: GenericValue -> GenericValue -> option GenericValue)
  gvs1 gvs2 ty : option t :=
  Some (fun gv3 => exists gv1, exists gv2, exists gv3',
    gv1 @ gvs1 /\ gv2 @ gvs2 /\ f gv1 gv2 = Some gv3' /\ (gv3 @ $ gv3' # ty $)).

Lemma lift_op1__inhabited : forall f gvs1 ty gvs2
  (H:forall x, exists z, f x = Some z),
  inhabited gvs1 -> 
  lift_op1 f gvs1 ty = Some gvs2 -> 
  inhabited gvs2.
Proof.
  intros. inv H1. inv H0.
  destruct (@H x) as [z J].
  destruct (@gv2gvs__inhabited z ty).
  exists x0. unfold Ensembles.In. exists x. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma lift_op2__inhabited : forall f gvs1 gvs2 ty gv3
  (H:forall x y, exists z, f x y = Some z),
  inhabited gvs1 -> inhabited gvs2 ->
  lift_op2 f gvs1 gvs2 ty = Some gv3 ->
  inhabited gv3.
Proof.
  intros. inv H0. inv H1. inv H2.
  destruct (@H x x0) as [z J].
  destruct (@gv2gvs__inhabited z ty).
  exists x1. unfold Ensembles.In. exists x. exists x0. exists z.
  rewrite J.
  repeat (split; auto).
Qed.

Lemma lift_op1__isnt_stuck : forall f gvs1 ty
  (H:forall x, exists z, f x = Some z),
  exists gvs2, lift_op1 f gvs1 ty = Some gvs2.
Proof.
  intros. unfold lift_op1. eauto.
Qed.

Lemma lift_op2__isnt_stuck : forall f gvs1 gvs2 ty
  (H:forall x y, exists z, f x y = Some z),
  exists gv3, lift_op2 f gvs1 gvs2 ty = Some gv3.
Proof.
  intros. unfold lift_op2. eauto.
Qed.

Lemma lift_op1__getTypeSizeInBits : forall S los nts f g t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y, x @ g -> f x = Some y -> 
   sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  gv @ gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8).
Proof.
  intros. inv H2.
  destruct H3 as [x [y [J1 [J2 J3]]]].
  apply H1 in J2; auto.
  eapply gv2gvs__getTypeSizeInBits; eauto.
Qed.

Lemma lift_op2__getTypeSizeInBits : forall S los nts f g1 g2 t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y z, x @ g1 -> y @ g2 -> f x y = Some z -> 
   sizeGenericValue z = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  gv @ gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8).
Proof.
  intros. inv H2.
  destruct H3 as [x [y [z [J1 [J2 [J3 J4]]]]]].
  apply H1 in J3; auto.
  eapply gv2gvs__getTypeSizeInBits; eauto.
Qed.

Lemma inhabited_inv : forall gvs, inhabited gvs -> exists gv, gv @ gvs.
Proof.
  intros. inv H; eauto.
Qed.

Lemma instantiate_undef__undef_gvs : forall gv t, gv @ (undef_gvs gv t).
Proof.
  intros. unfold undef_gvs.
  destruct t0; try solve [apply Union_introl; constructor | constructor].
  destruct f; try solve [apply Union_introl; constructor | constructor].
Qed.

Lemma instantiate_gv__gv2gvs : forall gv t, gv @ ($ gv # t $).
Proof.
  intros.
  destruct gv; simpl; try constructor.
  destruct p; simpl; try constructor.
  destruct v; simpl; try constructor.
  destruct gv; simpl; 
    try solve [constructor | auto using instantiate_undef__undef_gvs].  
Qed.

Lemma none_undef2gvs_inv : forall gv gv' t,
  gv @ $ gv' # t $ -> (forall mc, (Vundef, mc)::nil <> gv') -> gv = gv'.
Proof.
  intros.
  destruct gv'; try solve [inv H; auto].
  destruct p.
  destruct v; try solve [inv H; auto].
  destruct gv'; try solve [inv H; auto].
  assert (J:=@H0 m). congruence.
Qed.

End MNDGVs.

Definition NDGVs : GenericValues := mkGVs
MNDGVs.t
MNDGVs.instantiate_gvs
MNDGVs.inhabited
MNDGVs.cgv2gvs
MNDGVs.gv2gvs
MNDGVs.lift_op1
MNDGVs.lift_op2
MNDGVs.cgv2gvs__getTypeSizeInBits
MNDGVs.cgv2gvs__inhabited
MNDGVs.gv2gvs__getTypeSizeInBits
MNDGVs.gv2gvs__inhabited
MNDGVs.lift_op1__inhabited
MNDGVs.lift_op2__inhabited
MNDGVs.lift_op1__isnt_stuck
MNDGVs.lift_op2__isnt_stuck
MNDGVs.lift_op1__getTypeSizeInBits
MNDGVs.lift_op2__getTypeSizeInBits
MNDGVs.inhabited_inv
MNDGVs.instantiate_gv__gv2gvs
MNDGVs.none_undef2gvs_inv.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
