Require Import Common.
Require Import AilTypes.
Require Import Implementation.
Require Import AilTypesAux.
Require Import AilTyping.

Require Import AilTyping_proof.

Require Import GenTypes.
Require Import GenTypesAux.

Module D.
Require AilTyping_defns.
Require GenTypesAux_defns.

Include AilTyping_defns.
Include GenTypesAux_defns.
End D.

Module A.
Include AilTypesAux_defns.
Include AilTypesAux_proof.
End A.

Ltac genType_neg_tac :=
  match goal with
  | H : D.integer GenVoid |- _ => now inversion H
  | H : D.integer (GenArray _ _) |- _ => now inversion H
  | H : D.integer (GenFunction _ _) |- _ => now inversion H
  | H : D.integer (GenPointer _ _) |- _ => now inversion H
  | H : D.arithmetic GenVoid |- _ => now (inversion H; genType_neg_tac)
  | H : D.arithmetic (GenArray _ _) |- _ => now (inversion H; genType_neg_tac)
  | H : D.arithmetic (GenFunction _ _) |- _ => now (inversion H; genType_neg_tac)
  | H : D.arithmetic (GenPointer _ _) |- _ => now (inversion H; genType_neg_tac)
  | H : D.pointer GenVoid |- _ => now inversion H
  | H : D.pointer (GenArray _ _) |- _ => now inversion H
  | H : D.pointer (GenFunction _ _) |- _ => now inversion H
  | H : D.pointer (GenBasic _) |- _ => now inversion H
  | H : D.scalar GenVoid |- _ => now (inversion H; genType_neg_tac)
  | H : D.scalar (GenArray _ _) |- _ => now (inversion H; genType_neg_tac)
  | H : D.scalar (GenFunction _ _) |- _ => now (inversion H; genType_neg_tac)
  | H : ~ D.array (GenArray _ _) |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.function (GenFunction _ _) |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.pointer (GenPointer _ _) |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.arithmetic (GenBasic (GenInteger _)) |- _ => now (exfalso; apply H; do 2 constructor)
  | H : ~ D.integer    (GenBasic (GenInteger _)) |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.arithmetic (GenBasic ?gbt) |- _ => is_var gbt; destruct gbt
  | H : ~ D.integer    (GenBasic ?gbt) |- _ => is_var gbt; destruct gbt
  | H : ~ D.void GenVoid |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.function (GenFunction _ _) |- _ => now (exfalso; apply H; constructor)
  | H : ~ D.scalar (GenPointer _ _)       |- _ => now (exfalso; apply H; constructor; constructor)
  | H : ~ D.scalar (GenBasic ?gbt)         |- _ => is_var gbt; destruct gbt
  | H : ~ D.scalar (GenBasic (GenInteger _)) |- _ => now (exfalso; apply H; constructor 2; constructor)
  end.

Lemma interpret_genIntegerType_correct P git :
  optionSpec (interpret_genIntegerType P git) (D.interpretGenIntegerType P git).
Proof.
  induction git; simpl;
  unfold optionSpec;
  unfold option_bind;
  repeat match goal with
  | |- type_of_constant P ?ic = _ -> _ => case_fun (type_of_constant_correct P ic)
  | H : optionSpec (interpret_genIntegerType P ?git) _ |- interpret_genIntegerType P ?git = _ -> _ => case_fun H
  | _ => context_destruct
  end;
  solve [
    econstructor; solve [eassumption | apply A.integer_promotion_correct | apply A.usual_arithmetic_integer_correct]
  | inversion_clear 1;
    match goal with
    | H : forall _, ~ _ |- False => eapply H; eassumption
    end
  ].
Qed.

Lemma interpretGenIntegerType_functional {P} {git} {it1 it2} :
  D.interpretGenIntegerType P git it1 ->
  D.interpretGenIntegerType P git it2 ->
  it1 = it2.
Proof.
  revert it1 it2.
  induction git; inversion 1; inversion 1; subst;
  repeat match goal with
  | H1 : D.typeOfConstant P ?ic ?it1
  , H2 : D.typeOfConstant P ?ic ?it2 |- ?it1 = ?it2 => eapply typeOfConstant_functional; eassumption
  | IH : forall _ _, D.interpretGenIntegerType P ?git _ -> D.interpretGenIntegerType P ?git _ -> _ = _
  , H1 : D.interpretGenIntegerType P ?git ?it1
  , H2 : D.interpretGenIntegerType P ?git ?it2 |- _ => notSame it1 it2; assert (it1 = it2) by (eapply IH; eassumption); subst
  | H1 : A.integerPromotion P ?it ?it1
  , H2 : A.integerPromotion P ?it ?it2 |- ?it1 = ?it2 => eapply A.integerPromotion_functional; eassumption
  | H1 : A.usualArithmeticInteger P ?it1 ?it2 ?it3
  , H2 : A.usualArithmeticInteger P ?it1 ?it2 ?it3' |- ?it3 = ?it3' => eapply A.usualArithmeticInteger_functional; eassumption
  end; finish fail.
Qed.

Lemma interpretGenIntegerType_inject P it :
  D.interpretGenIntegerType P (inject_integerType it) it.
Proof. destruct it; my_auto. Qed.

Lemma interpret_genBasicType_correct P gbt :
  optionSpec (interpret_genBasicType P gbt) (D.interpretGenBasicType P gbt).
Proof.
  destruct gbt; simpl.
  unfold optionSpec.
  unfold option_bind.
  context_destruct.
  case_fun (interpret_genIntegerType_correct P git).
  - my_auto.
  - inversion_clear 1; firstorder.
Qed.

Lemma interpretGenBasicType_functional {P} {gbt} {bt1 bt2} :
  D.interpretGenBasicType P gbt bt1 ->
  D.interpretGenBasicType P gbt bt2 ->
  bt1 = bt2.
Proof.
  destruct gbt; inversion_clear 1; inversion_clear 1.
  apply f_equal; eapply interpretGenIntegerType_functional; eassumption.
Qed.

Lemma interpretGenBasicType_inject P bt :
  D.interpretGenBasicType P (inject_basicType bt) bt.
Proof. destruct bt; my_auto. Qed.

Lemma interpret_genType_correct P gt :
  optionSpec (interpret_genType P gt) (D.interpretGenType P gt).
Proof.
  destruct gt; simpl;
  unfold optionSpec;
  unfold option_bind;
  repeat match goal with
  | |- interpret_genBasicType P ?gbt = _ -> _ => case_fun (interpret_genBasicType_correct P gbt)
  | _ => context_destruct
  end; solve [finish fail | inversion_clear 1; firstorder].
Qed.

Lemma interpretGenType_functional {P} {gt} {t1 t2} :
  D.interpretGenType P gt t1 ->
  D.interpretGenType P gt t2 ->
  t1 = t2.
Proof.
  destruct gt;
  inversion_clear 1;
  inversion_clear 1;
  solve [
    my_auto
  | apply f_equal;
    eapply interpretGenBasicType_functional;
    eassumption
  ].
Qed.

Lemma interpretGenType_inject P t :
  D.interpretGenType P (inject_type t) t.
Proof.
  destruct t; my_auto.
  constructor; apply interpretGenBasicType_inject.
Qed.

Lemma interpret_genTypeCategory_correct P gtc :
  optionSpec (interpret_genTypeCategory P gtc) (D.interpretGenTypeCategory P gtc).
Proof.
  destruct gtc; simpl;
  unfold optionSpec;
  unfold option_bind;
  repeat match goal with
  | |- interpret_genType P ?gt = _ -> _ => case_fun (interpret_genType_correct P gt)
  | _ => context_destruct
  end; solve [my_auto | inversion_clear 1; firstorder].
Qed.

Lemma interpretGenTypeCategory_functional {P} {gtc} {tc1 tc2} :
  D.interpretGenTypeCategory P gtc tc1 ->
  D.interpretGenTypeCategory P gtc tc2 ->
  tc1 = tc2.
Proof.
  destruct gtc; inversion_clear 1; inversion_clear 1;
  solve [my_auto | apply f_equal; eapply interpretGenType_functional; eassumption].
Qed.

Lemma interpretGenTypeCategory_inject P tc :
  D.interpretGenTypeCategory P (inject_typeCategory tc) tc.
Proof.
  destruct tc; my_auto.
  constructor; apply interpretGenType_inject.
Qed.

Lemma array_correct gt : 
  boolSpec (array gt) (D.array gt).
Proof. destruct gt; my_auto. Qed.

Lemma array_interpret {gt} :
  D.array gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.array t.
Proof. inversion 1; inversion 1; my_auto. Qed.

Lemma array_inject {t} :
  A.array t ->
  D.array (inject_type t).
Proof. inversion 1; my_auto. Qed.

Lemma function_correct gt : 
  boolSpec (function gt) (D.function gt).
Proof. destruct gt; my_auto. Qed.

Lemma function_interpret {gt} {t} :
  D.function gt ->
  forall {P},
    D.interpretGenType P gt t ->
    A.function t.
Proof. inversion 1; inversion 1; my_auto. Qed.

(*
Lemma function_inject {t} :
  A.function t ->
  D.function (inject_type t).
Proof. inversion 1; my_auto. Qed.
*)

Lemma pointer_conversion_correct gt : 
  findSpec (pointer_conversion gt) (D.pointerConversion gt).
Proof. destruct gt; my_auto. Qed.

Lemma pointerConversion_functional {gt1 gt2 gt2'} :
  D.pointerConversion gt1 gt2  ->
  D.pointerConversion gt1 gt2' ->
  gt2 = gt2'.
Proof.
  inversion 1;
  inversion 1; subst;
  repeat match goal with
  | H : AilTypesAux_defns.unqualified _ |- _ => inversion_clear H
  end; finish ltac:(now genType_neg_tac).
Qed.

Lemma pointerConversion_interpret {gt1 gt2} {t1 t2} :
  D.pointerConversion gt1 gt2 ->
  forall {P},
    D.interpretGenType P gt1 t1 ->
    D.interpretGenType P gt2 t2 ->
    A.pointerConversion t1 t2.
Proof.
  inversion_clear 1;
  inversion 1; inversion 1; subst;
  repeat match goal with
  | H1 : D.interpretGenBasicType ?P ?gbt ?bt1
  , H2 : D.interpretGenBasicType ?P ?gbt ?bt2 |- _ =>
      notSame bt1 bt2;
      assert (bt1 = bt2)
        by (eapply interpretGenBasicType_functional; eassumption);
      subst
  | _ => genType_neg_tac
  end; now my_auto.
Qed.

(*
Lemma pointerConversion_inject {t1 t2} :
  A.pointerConversion t1 t2 ->
  D.pointerConversion (inject_type t1) (inject_type t2).
Proof.
  inversion 1; my_auto.
  destruct t2; my_auto; types_neg_tac.
Qed.
*)

Lemma integer_correct gt :
  boolSpec (integer gt) (D.integer gt).
Proof. destruct gt; my_auto. Qed.

Lemma integer_interpret {gt} :
  D.integer gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.integer t.
Proof.
  inversion_clear 1.
  inversion_clear 1.
  destruct bt; my_auto.
Qed.

Lemma integer_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.integer t ->
  D.integer gt.
Proof.
  inversion 1;
  inversion 1.
  destruct gbt.
  constructor.
Qed.

Lemma real_correct gt :
  boolSpec (real gt) (D.real gt).
Proof.
  destruct gt; my_auto;
  inversion_clear 1;
  genType_neg_tac.
Qed.

Lemma real_interpret {gt} :
  D.real gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.real t.
Proof.
  inversion 1; inversion 1; subst;
  solve [genType_neg_tac|constructor; eapply integer_interpret; eassumption].
Qed.

Lemma real_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.real t ->
  D.real gt.
Proof.
  inversion 1;
  inversion 1; subst;
  econstructor (eapply integer_inject; eassumption).
Qed.

Lemma pointer_correct gt :
  boolSpec (pointer gt) (D.pointer gt).
Proof. destruct gt; my_auto. Qed.

Lemma pointer_interpret {gt} :
  D.pointer gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.pointer t.
Proof. inversion 1; inversion 1; my_auto. Qed.

Lemma pointer_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.pointer t ->
  D.pointer gt.
Proof.
  inversion 1;
  inversion 1;
  constructor.
Qed.

Lemma arithmetic_correct gt : 
  boolSpec (arithmetic gt) (D.arithmetic gt).
Proof.
  do 2 unfold_goal.
  set (integer_correct gt).
  repeat (boolSpec_destruct; my_auto).
Qed.

Lemma arithmetic_interpret {gt} :
  D.arithmetic gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.arithmetic t.
Proof.
  inversion 1; inversion 1; my_auto.
  constructor; eapply integer_interpret; eassumption.
Qed.

Lemma arithmetic_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.arithmetic t ->
  D.arithmetic gt.
Proof.
  inversion 1;
  inversion 1; subst;
  econstructor (eapply integer_inject; eassumption).
Qed.

Lemma scalar_correct gt :
  boolSpec (scalar gt) (D.scalar gt).
Proof.
  do 2 unfold_goal.
  set (pointer_correct    gt).
  set (arithmetic_correct gt).
  repeat (boolSpec_destruct; my_auto).
Qed.

Lemma scalar_interpret {gt} :
  D.scalar gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.scalar t.
Proof.
  inversion 1; inversion 1; subst;
  solve [ my_auto | genType_neg_tac | econstructor (eapply arithmetic_interpret; eassumption) ].
Qed.

Lemma scalar_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.scalar t ->
  D.scalar gt.
Proof.
  inversion 1;
  inversion 1; subst;
  econstructor (
    solve [
      eapply pointer_inject; eassumption
    | eapply arithmetic_inject; eassumption ]
  ).
Qed.

Lemma void gt :
  boolSpec (void gt) (D.void gt).
Proof. destruct gt; my_auto. Qed.

Lemma void_interpret {gt} :
  D.void gt ->
  forall {P} {t},
    D.interpretGenType P gt t ->
    A.void t.
Proof. inversion 1; inversion 1; my_auto. Qed.

Lemma void_inject {P} {gt} {t} :
  D.interpretGenType P gt t ->
  A.void t ->
  D.void gt.
Proof. inversion 1; inversion 1; constructor. Qed.

Lemma pointer_to_complete_object_correct gt :
  if pointer_to_complete_object gt
  then exists q t', gt = GenPointer q t' /\ A.complete t'
  else ~ D.pointer gt \/ forall q t', gt = GenPointer q t' -> ~ A.complete t'.
Proof.
  unfold_goal.
  repeat match goal with
  | |- complete ?gt = _ -> _ => case_fun (A.complete_correct gt)
  | |- _ /\ _ => split
  | |- exists _ , _ => eexists; eexists; now intuition
  | _ => context_destruct
  end; right; congruence.
Qed.

Lemma pointers_to_compatible_complete_objects_correct gt1 gt2 :
  if pointers_to_compatible_complete_objects gt1 gt2
    then exists q1' t1' q2' t2',
           gt1 = GenPointer q1' t1' /\ gt2 = GenPointer q2' t2' /\
           A.complete t1' /\ A.complete t2' /\ A.compatible t1' t2'
    else ~ D.pointer gt1 \/ ~ D.pointer gt2
         \/ (forall q1' t1', gt1 = GenPointer q1' t1' -> ~ A.complete t1')
         \/ (forall q2' t2', gt2 = GenPointer q2' t2' -> ~ A.complete t2')
         \/ (forall q1' q2' t1' t2',
              gt1 = GenPointer q1' t1' ->
              gt2 = GenPointer q2' t2' -> ~ A.compatible t1' t2').
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- complete ?t = _ -> _] => case_fun (A.complete_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (A.compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _, _] => repeat eexists; now intuition
  | [|- ~ D.pointer ?t \/  _] =>
      match t with
      | GenPointer _ _ => fail 1
      | _           => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _ \/ _ \/ _] =>
      match t with
      | GenPointer _ _ => fail 1
      | _           => right; left; inversion 1
      end
  | [_ : ~ A.complete ?t1       |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; left; intros; congruence
  | [_ : ~ A.complete ?t2       |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; left; intros; congruence
  | [_ : ~ A.compatible ?t1 ?t2 |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointers_to_compatible_objects_correct gt1 gt2 :
  if pointers_to_compatible_objects gt1 gt2
    then exists q1' t1' q2' t2',
           gt1 = GenPointer q1' t1' /\ gt2 = GenPointer q2' t2' /\
           A.object t1'  /\ A.object t2' /\ A.compatible t1' t2'
    else ~ D.pointer gt1 \/ ~ D.pointer gt2
         \/ (forall q1' t1', gt1 = GenPointer q1' t1' -> ~ A.object t1')
         \/ (forall q2' t2', gt2 = GenPointer q2' t2' -> ~ A.object t2')
         \/ (forall q1' q2' t1' t2',
              gt1 = GenPointer q1' t1' ->
              gt2 = GenPointer q2' t2' -> ~ A.compatible t1' t2').
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (A.object_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (A.compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _ , _] => repeat eexists; intuition
  | [|- ~ D.pointer ?t \/ _ \/ _ \/ _ \/ _] =>
      match t with
      | GenPointer _ _ => fail 1
      | _           => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _ \/ _ \/ _] =>
      match t with
      | GenPointer _ _ => fail 1
      | _           => right; left; inversion 1
      end
  | [_ : ~ A.object ?t1         |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; left; intros; congruence
  | [_ : ~ A.object ?t2         |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; left; intros; congruence
  | [_ : ~ A.compatible ?t1 ?t2 |- _ \/ _ \/ _ \/ _ \/ _ ] => right; right; right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointer_to_object_correct gt :
  if pointer_to_object gt
    then exists q t', gt = GenPointer q t' /\ A.object t'
    else ~ D.pointer gt \/ forall q t', gt = GenPointer q t' -> ~ A.object t'.
Proof.
  unfold_goal.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (A.object_correct t)
  | [|- _ /\ _] => split
  | [|- exists _ , _] => repeat eexists; intuition
  | [|- ~ D.pointer ?t \/ _] =>
      match t with
      | GenPointer _ _ => right
      | _              => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointer_to_void_correct gt :
  if pointer_to_void gt
    then exists q t', gt = GenPointer q t' /\ A.void t'
    else ~ D.pointer gt \/ forall q t', gt = GenPointer q t' -> ~ A.void t'.
Proof.
  unfold_goal.
  repeat match goal with
  | [|- void ?t = _ -> _] => case_fun (A.void_correct t)
  | [|- ~ _] => intros [? [? [? ?]]]
  | [|- _ /\ _] => split
  | [|- exists _ , _] => repeat eexists; now intuition
  | [|- ~ D.pointer ?t \/ _] =>
      match t with
      | GenPointer _ _ => right; intros; inversion 1
      | _              => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointers_to_compatible_types_correct gt1 gt2 :
  if pointers_to_compatible_types gt1 gt2
    then exists q1' t1' q2' t2',
           gt1 = GenPointer q1' t1' /\ gt2 = GenPointer q2' t2' /\
           A.compatible t1' t2'
    else ~ D.pointer gt1 \/ ~ D.pointer gt2
         \/ (forall q1' q2' t1' t2',
              gt1 = GenPointer q1' t1' ->
              gt2 = GenPointer q2' t2' -> ~ A.compatible t1' t2').
Proof.
  unfold_goal.
  repeat match goal with
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (A.compatible_correct t1 t2)
  | [|- _ /\ _] => split
  | [|- exists _ , _] => repeat eexists; now intuition 
  | [|- ~ D.pointer ?t \/ _ \/ _ ] =>
      match t with
      | GenPointer _ _ => fail 1
      | _              => left; inversion 1
      end
  | [|- _ \/ ~ D.pointer ?t \/ _ ] =>
      match t with
      | GenPointer _ _ => fail 1
      | _              => right; left; inversion 1
      end
  | [_ : ~ A.compatible ?t1 ?t2 |- _ \/ _ \/ _ ] => right; right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Definition integer_promotion_correct git :
  findSpec (integer_promotion git) (D.integerPromotion git).
Proof. induction git; my_auto. Qed.

Definition integerPromotion_functional {git1 git2 git2'} :
  D.integerPromotion git1 git2 ->
  D.integerPromotion git1 git2' ->
  git2 = git2'.
Proof. inversion 1; inversion 1; my_auto. Qed.

Definition integerPromotion_interpret {git1 git2} :
  D.integerPromotion git1 git2 ->
  forall {P} {it1 it2},
    D.interpretGenIntegerType P git1 it1 ->
    D.interpretGenIntegerType P git2 it2 ->
    A.integerPromotion P it1 it2.
Proof.
  inversion_clear 1.
  inversion_clear 2.
  match goal with
  | H1 : D.interpretGenIntegerType P ?git ?it1
  , H2 : D.interpretGenIntegerType P ?git ?it2 |- _ =>
      notSame it1 it2;
      assert (it1 = it2)
        by (eapply interpretGenIntegerType_functional; eassumption);
      subst
  end.
  assumption.
Qed.

Lemma integerPromotion_inject {P} {it1 it2} {git1} :
  A.integerPromotion P it1 it2 ->
  D.interpretGenIntegerType P git1 it1 ->
  exists git2,
    D.interpretGenIntegerType P git2 it2 /\
    D.integerPromotion git1 git2.
Proof.
  intros ? ?.
  exists (Promote git1).
  split.
  - econstructor; eassumption.
  - constructor.
Qed.

Definition integerPromotion_promoted {git1 git2} :
  D.integerPromotion git1 git2 ->
  D.promoted git2.
Proof. inversion_clear 1; my_auto. Qed.

Lemma promotion_correct gt :
  optionSpec (promotion gt) (D.promotion gt).
Proof. destruct gt; my_auto. Qed.

Lemma promotion_functional {gt1 gt2 gt2'} :
  D.promotion gt1 gt2  ->
  D.promotion gt1 gt2' ->
  gt2 = gt2'.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  repeat apply f_equal; eapply integerPromotion_functional; eassumption.
Qed.

Definition promotion_interpret {gt1 gt2} :
  D.promotion gt1 gt2 ->
  forall {P} {t1 t2},
    D.interpretGenType P gt1 t1 ->
    D.interpretGenType P gt2 t2 ->
    A.promotion P t1 t2.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  inversion_clear 1.
  repeat match goal with
  | H : D.interpretGenBasicType P _ _ |- _ => inversion_clear H
  end.
  constructor; eapply integerPromotion_interpret; eassumption.
Qed.

Lemma promotion_inject {P} {t1 t2} {gt1} :
  A.promotion P t1 t2 ->
  D.interpretGenType P gt1 t1 ->
  exists gt2,
    D.interpretGenType P gt2 t2 /\
    D.promotion gt1 gt2.
Proof.
  inversion_clear 1;
  inversion_clear 1.
  match goal with
  | H : D.interpretGenBasicType P _ _ |- _ => inversion_clear H
  end.
  match goal with
  | H1 : A.integerPromotion P it1 it2
  , H2 : D.interpretGenIntegerType P _ ?it1 |- _ =>
      destruct (integerPromotion_inject H1 H2) as [git2 []]
  end.
  exists (GenBasic (GenInteger git2)).
  split; repeat constructor; assumption.
Qed.

Lemma promoted_interpret {git} :
  D.promoted git ->
  forall {P} {it},
    D.interpretGenIntegerType P git it ->
    A.promoted it.
Proof.
  inversion_clear 1;
  inversion_clear 1.
  eapply AilTypesAux_proof.integerPromotion_promoted; eassumption.
Qed.

Lemma promoted_integerPromotion {P} {it} :
  A.promoted it ->
  A.integerPromotion P it it.
Proof.
  pose (A.le_integer_rank_correct P it (Signed Int)).
  inversion 1; econstructor (now my_auto).
Qed.

Lemma promoted_inject {P} {it} :
  A.promoted it ->
  {git : genIntegerType &
    D.interpretGenIntegerType P git it *
    D.promoted git
  }.
Proof.
  exists (Promote (Concrete it)).
  split.
  - econstructor.
    + econstructor.
    + apply promoted_integerPromotion; assumption.
  - constructor.
Qed.

Lemma usual_arithmetic_promoted_integer_correct git1 git2 :
  D.promoted git1 ->
  D.promoted git2 ->
  findSpec (usual_arithmetic_promoted_integer git1 git2) (D.usualArithmeticPromotedInteger git1 git2).
Proof. constructor. Qed.

Lemma usualArithmeticPromotedInteger_functional {git1 git2 git3 git3'} :
  D.usualArithmeticPromotedInteger git1 git2 git3  ->
  D.usualArithmeticPromotedInteger git1 git2 git3' ->
  git3 = git3'.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  congruence.
Qed.

Lemma usualArithmeticPromotedInteger_interpret {git1 git2 git3} :
  D.promoted git1 ->
  D.promoted git2 ->
  D.usualArithmeticPromotedInteger git1 git2 git3 ->
  forall {P} {it1 it2 it3},
    D.interpretGenIntegerType P git1 it1 ->
    D.interpretGenIntegerType P git2 it2 ->
    D.interpretGenIntegerType P git3 it3 ->
    A.usualArithmeticPromotedInteger P it1 it2 it3.
Proof.
  inversion_clear 3;
  inversion_clear 3.
  repeat match goal with
  | H1 : D.interpretGenIntegerType P ?git ?it1
  , H2 : D.interpretGenIntegerType P ?git ?it2 |- _ =>
      notSame it1 it2; assert (it1 = it2) by exact (interpretGenIntegerType_functional H1 H2); subst
  end.
  repeat match goal with
  | H : D.promoted ?git, _ : D.interpretGenIntegerType P ?git ?it |- _ =>
    notHyp (A.promoted it);
    assert (A.promoted it)
      by (eapply promoted_interpret; [eexact H | eassumption])
  end.
  match goal with
  | H : A.usualArithmeticInteger P _ _ _ |- _ => inversion_clear H
  end.
  repeat match goal with
  | H : A.integerPromotion P ?it1 ?it2 |- _ =>
      notSame it1 it2;
      assert (it1 = it2)
        by (eapply AilTypesAux_proof.integerPromotion_functional; [eapply promoted_integerPromotion; eassumption | eassumption]);
      subst
  end.
  assumption.
Qed.

Lemma usualArithmeticPromotedInteger_inject {P} {it1 it2 it3} {git1 git2} :
  A.promoted it1 ->
  A.promoted it2 ->
  A.usualArithmeticPromotedInteger P it1 it2 it3 ->
  D.promoted git1 ->
  D.promoted git2 ->
  D.interpretGenIntegerType P git1 it1 ->
  D.interpretGenIntegerType P git2 it2 ->
  exists git3,
    D.interpretGenIntegerType P git3 it3 /\
    D.usualArithmeticPromotedInteger git1 git2 git3.
Proof.
  intros.
  exists (usual_arithmetic_promoted_integer git1 git2); split.
  - econstructor.
    + eassumption.
    + eassumption.
    + econstructor;
      solve [eapply promoted_integerPromotion; eassumption | eassumption].
  - apply usual_arithmetic_promoted_integer_correct; assumption.
Qed.

Lemma usual_arithmetic_integer_correct git1 git2 :
  findSpec (usual_arithmetic_integer git1 git2) (D.usualArithmeticInteger git1 git2).
Proof.
  unfold usual_arithmetic_integer.
  set (integer_promotion_correct git1).
  set (integer_promotion_correct git2).
  econstructor;
  repeat first [
    eassumption
  | eapply usual_arithmetic_promoted_integer_correct
  | eapply integerPromotion_promoted
  ].
Qed.

Lemma usualArithmeticInteger_functional {git1 git2 git3 git3'} :
  D.usualArithmeticInteger git1 git2 git3  ->
  D.usualArithmeticInteger git1 git2 git3' ->
  git3 = git3'.
Proof.
  inversion_clear 1;
  inversion_clear 1.
  repeat match goal with
  | H1 : D.integerPromotion ?git ?git1, H2 : D.integerPromotion ?git ?git2 |- _ =>
      notSame git1 git2;
      assert (git1 = git2)
        by (eapply integerPromotion_functional; eassumption);
      subst
  end.
  eapply usualArithmeticPromotedInteger_functional; eassumption.
Qed.

Lemma interpret_integerPromotion {git1 git2} :
  D.integerPromotion git1 git2 ->
  forall {P} {it1},
    D.interpretGenIntegerType P git1 it1 ->
    exists it2,
      D.interpretGenIntegerType P git2 it2.
Proof.
  inversion_clear 1.
  intros.
  exists (AilTypesAux.integer_promotion P it1).
  econstructor.
  - eassumption.
  - eapply A.integer_promotion_correct.
Qed.

Lemma usualArithmeticInteger_interpret {git1 git2 git3} :
  D.usualArithmeticInteger git1 git2 git3 ->
  forall {P} {it1 it2 it3},
    D.interpretGenIntegerType P git1 it1 ->
    D.interpretGenIntegerType P git2 it2 ->
    D.interpretGenIntegerType P git3 it3 ->
    A.usualArithmeticInteger P it1 it2 it3.
Proof.
  inversion_clear 1.
  intros.
  match goal with
  | H1 : D.integerPromotion git1 _
  , H2 : D.interpretGenIntegerType P git1 _ |- _ =>
      destruct (interpret_integerPromotion H1 H2)
  end.
  match goal with
  | H1 : D.integerPromotion git2 _
  , H2 : D.interpretGenIntegerType P git2 _ |- _ =>
      destruct (interpret_integerPromotion H1 H2)
  end.
  econstructor;
  match goal with
  | H : D.integerPromotion ?git1 ?git2
  , H1 : D.interpretGenIntegerType P ?git1 ?it1
  , H2 : D.interpretGenIntegerType P ?git2 ?it2 |- A.integerPromotion P ?it1 _ =>
      apply (integerPromotion_interpret H H1 H2)
  | H1 : D.integerPromotion git1 _
  , H2 : D.integerPromotion git2 _ |- A.usualArithmeticPromotedInteger P _ _ it3 =>
      eapply (usualArithmeticPromotedInteger_interpret (integerPromotion_promoted H1) (integerPromotion_promoted H2));
      eassumption
  end.
Qed.

Lemma usualArithmeticInteger_inject {P} {it1 it2 it3} {git1 git2} :
  A.usualArithmeticInteger P it1 it2 it3 ->
  D.interpretGenIntegerType P git1 it1 ->
  D.interpretGenIntegerType P git2 it2 ->
  exists git3,
    D.interpretGenIntegerType P git3 it3 /\
    D.usualArithmeticInteger git1 git2 git3.
Proof.
  intros H ? ?.
  exists (usual_arithmetic_integer git1 git2); split.
  - inversion_clear H.
    do 2 econstructor;
    repeat first [
      eassumption
    | eapply promoted_integerPromotion
    | eapply A.integerPromotion_promoted
    ].
  - econstructor.
    + exact (integer_promotion_correct git1).
    + exact (integer_promotion_correct git2).
    + apply usual_arithmetic_promoted_integer_correct; now econstructor.
Qed.

Lemma usual_arithmetic_correct gt1 gt2 :
  optionSpec (usual_arithmetic gt1 gt2) (D.usualArithmetic gt1 gt2).
Proof.
  destruct gt1, gt2; my_auto.
  constructor; apply usual_arithmetic_integer_correct.
Qed.

Lemma usualArithmetic_functional {gt1 gt2 gt3 gt3'} :
  D.usualArithmetic gt1 gt2 gt3  ->
  D.usualArithmetic gt1 gt2 gt3' ->
  gt3 = gt3'.
Proof.
  inversion_clear 1;
  inversion_clear 1.
  repeat apply f_equal.
  eapply usualArithmeticInteger_functional; eassumption.
Qed.

Lemma usualArithmetic_interpret {gt1 gt2 gt3} :
  D.usualArithmetic gt1 gt2 gt3 ->
  forall {P} {t1 t2 t3},
    D.interpretGenType P gt1 t1 ->
    D.interpretGenType P gt2 t2 ->
    D.interpretGenType P gt3 t3 ->
    A.usualArithmetic P t1 t2 t3.
Proof.
  repeat inversion_clear 1.
  repeat match goal with
  | H : D.interpretGenBasicType P _ _ |- _ => inversion_clear H
  end.
  constructor; eapply usualArithmeticInteger_interpret; eassumption.
Qed.

Lemma usualArithmetic_inject {P} {t1 t2 t3} {gt1 gt2} :
  A.usualArithmetic P t1 t2 t3 ->
  D.interpretGenType P gt1 t1 ->
  D.interpretGenType P gt2 t2 ->
  exists gt3,
    D.interpretGenType P gt3 t3 /\
    D.usualArithmetic gt1 gt2 gt3.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  inversion_clear 1.
  repeat match goal with
  | H : D.interpretGenBasicType P _ _ |- _ => inversion_clear H
  end.
  match goal with
  | H  : A.usualArithmeticInteger P ?it1 ?it2 _
  , H1 : D.interpretGenIntegerType P _ ?it1
  , H2 : D.interpretGenIntegerType P _ ?it2 |- _ =>
        destruct (usualArithmeticInteger_inject H H1 H2) as [git3 []]
  end.
  exists (GenBasic (GenInteger git3)); repeat constructor; assumption.
Qed.

(*Require Import ZArith.

Local Open Scope Z.

Definition counter : implementation.
  refine (make_implementation
    Two'sComplement
    ( fun it =>
        match it with
        | Char | Signed   _ => true
        | Bool | Unsigned _ => false
        end
    )
    ( fun it =>
        match it with
        | Char => 7
        | Bool => 2
        | Signed   Ichar => 7
        | Unsigned Ichar => 8
        | Signed   Short => 15
        | Unsigned Short => 16
        | Signed   Int      => 127
        | Unsigned Int      => 128
        | Signed   Long     => 127
        | Unsigned Long     => 256
        | Signed   LongLong => 255
        | Unsigned LongLong => 256
        end
    )
    (Unsigned Long)
    (Signed   Long)
    (fun _ => eq_refl)
    eq_refl
    (fun _ => eq_refl)
    eq_refl
    eq_refl
    _
    _
    eq_refl
    _
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    (fun ibt => match ibt with Ichar => _ | Short => _ | Int => _ | Long => _ | LongLong => _ end)
    _ _ _ _ _ _ _ _ _ _);
  simpl; try omega.
Defined.

Eval compute in usual_arithmetic_promoted_integer counter (Signed Long) (usual_arithmetic_promoted_integer counter (Unsigned Int) (Signed LongLong)).
Eval compute in usual_arithmetic_promoted_integer counter (usual_arithmetic_promoted_integer counter (Signed Long) (Unsigned Int)) (Signed LongLong).
Eval compute in lt_Z (precision counter (Unsigned Long)) (precision counter (Signed LongLong)) (*false*).
Eval compute in lt_Z (precision counter (Unsigned Int)) (precision counter (Signed Long)) (*false*).
Eval compute in lt_Z (precision counter (Unsigned Int)) (precision counter (Signed LongLong)) (*true*).
*)
