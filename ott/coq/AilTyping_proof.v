Require Program.Tactics.

Require Import Common.
Require Import AilTypes AilTypes_proof.
Require Import AilSyntax AilSyntax_proof.
Require Import AilSyntaxAux AilSyntaxAux_proof.
Require Import AilTypesAux AilTypesAux_proof.
Require Import AilWf AilWf_proof.
Require Import AilTyping.

Module D.
  Require AilTyping_defns.

  Include Context_defns.
  Include AilTyping_defns.
  Include AilTypesAux_defns.
End D.

Lemma wellTypedBinaryArithmetic_arithmetic {aop} {t1 t2} :
  D.wellTypedBinaryArithmetic t1 aop t2 ->
  D.arithmetic t1 * D.arithmetic t2.
Proof.
  inversion 1;
  repeat match goal with
  | [H : D.integer _ |- _ ] => apply D.Arithmetic_Integer in H
  end; split; assumption.
Qed.

Lemma type_of_constant_correct P ic :
  optionSpec (type_of_constant P ic) (D.typeOfConstant P ic).
Proof.
  unfold_goal; destruct ic; simpl;
  repeat match goal with
  | |- in_integer_range _ ?n ?it = _ -> _ => case_fun (in_integer_range_correct P n it)
  | [H : ~ D.inIntegerRange _ ?n (Signed Long) |- _] =>
      set (Program.Basics.compose H inIntegerRange_Signed_Int_Long);
      contradiction
  | [H : ~  D.inIntegerRange _ ?n (Unsigned Long) |- _] =>
      set (Program.Basics.compose H inIntegerRange_Unsigned_Int_Long);
      contradiction
  | [|- D.typeOfConstant _ _ _] => econstructor (eassumption)
  | [|- forall _, neg (D.typeOfConstant _ _ _)] => inversion 1; subst
  | [|- forall _, D.typeOfConstant _ _ _ -> _ = _] => inversion 1; subst
  | [|-  _ * _] => split
  | _ => context_destruct
  end; solve [congruence | contradiction].
Qed.

Lemma type_of_constant_unique P ic :
  optionUnique (type_of_constant P ic) (D.typeOfConstant P ic).
Proof.
  unfold_goal; destruct ic; simpl;
  repeat match goal with
  | |- in_integer_range P ?n ?it = _ -> _ => case_fun (in_integer_range_correct P n it)
  | [H : ~ D.inIntegerRange P ?n (Signed Long) |- _] =>
      set (Program.Basics.compose H inIntegerRange_Signed_Int_Long);
      contradiction
  | [H : ~ D.inIntegerRange P ?n (Unsigned Long) |- _] =>
      set (Program.Basics.compose H inIntegerRange_Unsigned_Int_Long);
      contradiction
  | [|- D.typeOfConstant _ _ _] => econstructor (eassumption)
  | [|- forall _, neg (D.typeOfConstant _ _ _)] => inversion 1; subst
  | [|- forall _, D.typeOfConstant _ _ _ -> _ = _] => inversion 1; subst
  | [|-  _ * _] => split
  | _ => context_destruct
  end; solve [congruence | contradiction].
Qed.

Lemma typeOfConstant_functional {P} {ic} {it1 it2} :
  D.typeOfConstant P ic it1 ->
  D.typeOfConstant P ic it2 ->
  it1 = it2.
Proof.
  intros H1 H2.
  set (type_of_constant_unique _ _ _ H1).
  set (type_of_constant_unique _ _ _ H2).
  congruence.
Qed.

Lemma typeOfExpression_sub {A B} {P} {G1 G2:gamma} {S:sigma A B} {e} :
  D.subP (fun v => D.fv v e) eq G1 G2 ->
  forall t,
    D.typeOfExpression P G1 S e t ->
    D.typeOfExpression P G2 S e t.
Proof.
  apply (
    expression_nrect
      (fun x => forall (Hfree : D.subP (fun v => D.fv'         v x) eq G1 G2) t (T1 : D.typeOfExpression' P G1 S x t), D.typeOfExpression' P G2 S x t)
      (fun x => forall (Hfree : D.subP (fun v => D.fv          v x) eq G1 G2) t (T1 : D.typeOfExpression  P G1 S x t), D.typeOfExpression  P G2 S x t)
      (fun x => forall (Hfree : D.subP (fun v => D.fvArguments v x) eq G1 G2) t (T1 : D.typeOfArguments   P G1 S x t), D.typeOfArguments   P G2 S x t)
  ); intros; inversion_clear T1;
  match goal with
  | H : D.assignable   P G1 S _ _   |- _ => inversion H; subst
  | _ => idtac
  end;
  repeat match goal with
  | H : D.typeOfLValue P G1 S _ _ _ |- _ => inversion_clear H
  | H : D.typeOfRValue P G1 S _ _   |- _ => inversion_clear H
  | H : D.typeOfExpression _ G1 _ ?e _, IH : D.subP (fun _ => D.fv _ ?e) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fv v e) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fv v e) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.typeOfExpression' _ G1 _ ?e _, IH : D.subP (fun _ => D.fv' _ ?e) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fv' v e) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fv' v e) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.typeOfArguments _ G1 _ ?es _, IH : D.subP (fun _ => D.fvArguments _ ?es) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fvArguments v es) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fvArguments v es) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.lookup G1 ?v _ |- D.typeOfExpression' _ G2 _ (Var ?v) _ =>
      constructor; destruct (Hfree _ (D.Fv'_Var v) _ H) as [? [? ?]]; congruence
  end;
  econstructor (
      solve [ eassumption
            | econstructor (
                solve [ econstructor (
                          solve [ econstructor (solve [ econstructor (eassumption)
                                                      | eassumption])
                                | eassumption])
                      | eassumption])
            ]
  ).
Qed.

Lemma type_of_rvalue_correct_aux {A B} {P} {G} {S : sigma A B} {e} :
  optionSpec   (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  optionSpec   (type_of_rvalue P G S e) (D.typeOfRValue P G S e).
Proof.
  intros type_of_expression_correct type_of_expression_unique.
  do 3 unfold_goal.
  optionSpec_destruct;
  repeat match goal with
  | [|- lvalue_conversion ?t = _ -> _] => case_fun (lvalue_conversion_correct t)
  | _ => context_destruct
  end;
  solve
    [ econstructor (
          solve [ eassumption
                | my_auto
                | apply pointer_conversion_correct]
        )
    | inversion_clear 1;
      repeat match goal with
      | H : D.typeOfLValue     P G S _ _ _ |- _ => inversion_clear H
      | H : D.typeOfExpression P G S _ _   |- _ =>
          let Heq := fresh in
          set (type_of_expression_unique _ H) as Hfresh;
          congruence || Tactics.autoinjections; now firstorder
      end
    ].
Qed.

Lemma type_of_rvalue_unique_aux {A B} {P} {G} {S : sigma A B} {e} :
  optionSpec   (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  optionUnique (type_of_rvalue P G S e) (D.typeOfRValue P G S e).
Proof.
  intros type_of_expression_correct type_of_expression_unique ? ?.
  do 2 unfold_goal.
  repeat match goal with
  | _ => optionSpec_destruct
  | |- context[lvalue_conversion  ?t] => set (lvalue_conversion_correct  t)
  | |- context[pointer_conversion ?t] => notHyp (findSpec (pointer_conversion t) (D.pointerConversion t));
                                         set (pointer_conversion_correct t)
  | _ => context_destruct
  end;
  repeat match goal with
  | H : D.typeOfLValue     P G S _ _ _ |- _ => inversion_clear H
  | H : D.typeOfRValue     P G S _ _   |- _ => inversion_clear H
  | H : D.typeOfExpression P G S _ _   |- _ =>
      let Heq := fresh in
      set (type_of_expression_unique _ H) as Hfresh;
      discriminate Hfresh || Tactics.autoinjections
  end;
  solve [ apply f_equal; eapply (lvalueConversion_functional ); eassumption
        | apply f_equal; eapply (pointerConversion_functional); eassumption
        | now firstorder ].
Qed.

Lemma typeOfExpression_functional_aux {A B} {P} {G} {S : sigma A B} {e} :
  optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  forall {tc tc'},
    D.typeOfExpression P G S e tc  ->
    D.typeOfExpression P G S e tc' ->
    tc = tc'.
Proof.
  intros type_of_expression_unique ? ? H1 H2.
  set (type_of_expression_unique _ H1).
  set (type_of_expression_unique _ H2).
  congruence.
Qed.

Lemma typeOfRValue_functional_aux {A B} {P} {G} {S : sigma A B} {e} :
  optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e) ->
  forall {t t'},
    D.typeOfRValue P G S e t  ->
    D.typeOfRValue P G S e t' ->
    t = t'.
Proof.
  intros type_of_expression_unique.
  inversion_clear 1; inversion_clear 1;
  repeat match goal with
  | H : D.typeOfLValue P G S _ _ _ |- _ => inversion_clear H
  end;
  match goal with
  | H1 : D.typeOfExpression P G S ?e _
  , H2 : D.typeOfExpression P G S ?e _ |- _ =>
      let Heq := fresh in
      set (typeOfExpression_functional_aux type_of_expression_unique H1 H2) as Heq;
      discriminate Heq || Tactics.autoinjections
  end;
  solve [
      eapply pointerConversion_functional; eassumption
    | eapply lvalueConversion_functional ; eassumption ].
Qed.

Lemma type_of_rvalue_lvalue_eq {A B} {P} {G} {S : sigma A B} {e} {q1} {t1 t2} :
  type_of_expression P G S e = Some (LValueType q1 t1) ->
  type_of_rvalue P G S e = Some t2 ->
  t1 = t2.
Proof.
  intros Heq.
  do 2 unfold_goal.
  rewrite Heq.
  destruct t1; my_auto.
Qed.

Lemma type_of_rvalue_aux_lvalue_eq_lift {A B} {P} {G} {S : sigma A B} {e} {q1} {t1 t2}:
  D.typeOfExpression P G S e (LValueType q1 t1) ->
  type_of_expression P G S e = Some (LValueType q1 t1) ->
  type_of_rvalue P G S e = Some t2 ->
  D.typeOfRValue P G S e t1.
Proof.
  intros ? Heq1 Heq2.
  rewrite <- (type_of_rvalue_lvalue_eq Heq1 Heq2) in Heq2.
  revert Heq2.
  do 2 unfold_goal.
  rewrite Heq1.
  unfold_goal.
  context_destruct.
  case_fun (lvalue_convertible_correct t1).
  + injection 1; intros Heq3.
    set (pointer_conversion_correct t1) as Hpc.
    rewrite Heq3 in Hpc.
    econstructor 2.
    * econstructor; eassumption.
    * econstructor; eassumption.
  + discriminate.
Qed.

Ltac types_neg_tac :=
  match goal with
  | [H : D.complete Void |- _ ] => inversion H
  | [H : D.object (Function _ _) |- _ ] => inversion H
  | [H : D.integer Void           |- _ ] => inversion H
  | [H : D.integer (Array _ _) |- _ ] => inversion H
  | [H : D.integer (Function _ _) |- _ ] => inversion H
  | [H : D.integer (Pointer  _ _) |- _ ] => inversion H
  | [H : D.arithmetic Void           |- _ ] => inversion_clear H
  | [H : D.arithmetic (Array    _ _) |- _ ] => inversion_clear H
  | [H : D.arithmetic (Function _ _) |- _ ] => inversion_clear H
  | [H : D.arithmetic (Pointer  _ _) |- _ ] => inversion_clear H
  | [H : D.scalar Void           |- _ ] => inversion_clear H
  | [H : D.scalar (Array _ _) |- _ ] => inversion_clear H
  | [H : D.scalar (Function _ _) |- _ ] => inversion_clear H
  | [H : D.pointer (Basic _) |- _] => inversion H
  | [H : D.pointer (Array _ _) |- _] => inversion H
  | [H : D.pointer (Function _ _) |- _] => inversion H
  | [H : D.pointer Void |- _] => inversion H
  | [H : neg (D.pointer (Pointer _ _)) |- _ ] => exfalso; apply H; now constructor
  | [H : neg (D.void Void) |- _ ] => exfalso; apply H; now constructor
  | [H : neg (D.object Void) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.object (Basic _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.object (Pointer _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.object (Array _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.complete (Basic _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.complete (Pointer _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.complete (Array _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.pointer (Pointer _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.arithmetic (Basic (Integer _))) |- _ ] => exfalso; apply H; do 2 constructor
  | [H : neg (D.integer    (Basic (Integer _))) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.arithmetic (Basic ?bt)) |- _ ] => is_var bt; destruct bt
  | [H : neg (D.integer    (Basic ?bt)) |- _ ] => is_var bt; destruct bt
  | [H : neg (D.void Void) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.boolean Bool) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.function (Function _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.array (Array _ _)) |- _ ] => exfalso; apply H; constructor
  | [H : neg (D.scalar (Pointer _ _)) |- _ ] => exfalso; apply H; constructor; constructor
  | [H : neg (D.scalar (Basic ?bt)) |- _ ] => is_var bt; destruct bt
  | [H : neg (D.scalar (Basic (Integer _))) |- _ ] => exfalso; apply H; constructor 2; constructor
  | [H : D.void (Array _ _)    |- _ ] => inversion H
  | [H : D.void (Function _ _) |- _ ] => inversion H
  | [H : D.void (Pointer  _ _) |- _ ] => inversion H
  | [H : D.void (Basic _)      |- _ ] => inversion H
  | [H : D.boolean Void        |- _ ] => inversion H
  | [H : D.boolean (Array _ _)    |- _ ] => inversion H
  | [H : D.boolean (Function _ _) |- _ ] => inversion H
  | [H : D.boolean (Pointer  _ _) |- _ ] => inversion H
  | [H : D.boolean Void        |- _ ] => inversion H
  | [H : D.boolean (Array _ _)    |- _ ] => inversion H
  | [H : D.boolean (Function _ _) |- _ ] => inversion H
  | [H : D.boolean (Basic _) |- _ ] => inversion H
  | H : D.wellTypedBinaryArithmetic (Pointer _ _) Add _ |- _ => inversion_clear H
  | H : D.wellTypedBinaryArithmetic _ Add (Pointer _ _) |- _ => inversion_clear H
  end.

Ltac types_elaborate_tac :=
  match goal with
  | H : D.void ?t |- _ => is_var  t; inversion H; subst
  | H : D.boolean ?t |- _ => is_var  t; inversion H; subst
  | H : D.pointer ?t |- _ => is_var t; inversion H; subst
  | H : D.compatible Void ?t |- _ => is_var t; inversion H; subst
  | H : D.compatible ?t Void |- _ => is_var t; inversion H; subst
  | H : D.composite Void Void ?t |- _ => is_var t; inversion H; subst
  | H : D.unqualified ?q |- _ => is_var q; inversion H; subst
  end.

Ltac types_tac :=
  repeat first [types_neg_tac | types_elaborate_tac | finish fail].

Lemma assignable_correct_aux {A B} {P} {G} {S : sigma A B} {t1} {e2} :
  optionSpec   (type_of_expression P G S e2) (D.typeOfExpression P G S e2) ->
  optionUnique (type_of_expression P G S e2) (D.typeOfExpression P G S e2) ->
  boolSpec (assignable P G S t1 e2) (D.assignable P G S t1 e2).
Proof.
  intros type_of_expression_correct type_of_expression_unique.
  set (type_of_rvalue_correct_aux type_of_expression_correct type_of_expression_unique).
  set (type_of_rvalue_unique_aux  type_of_expression_correct type_of_expression_unique) as type_of_rvalue_unique.
  do 3 unfold_goal.
  unfold well_typed_assignment.
  unfold andb.
  unfold orb.
  repeat match goal with
  | |- arithmetic ?t           = _  -> _ => case_fun (arithmetic_correct t)
  | |- null_pointer_constant ?e2 = _  -> _ => case_fun (null_pointer_constant_correct e2)
  | |- compatible ?t1 ?t2    = _  -> _ => case_fun (compatible_correct t1 t2)
  | |- boolean ?t                 = _  -> _ => case_fun (boolean_correct t)
  | |- void ?t                 = _  -> _ => case_fun (void_correct t)
  | |- object ?t               = _  -> _ => case_fun (object_correct t)
  | |- sub_qualifiers ?q1 ?q2       = ?o -> _ => destruct o; intros ?
  | _ => optionSpec_destruct
  | _ => context_destruct
  end; 
  solve [
      econstructor (solve [econstructor (eassumption) | eassumption])
    | inversion 1; my_auto;
      match goal with
      | H : D.typeOfRValue P G S e2 _ |- _ =>
          let Heq := fresh in
          set (type_of_rvalue_unique _ H) as Heq;
          discriminate Heq || injection Heq; intros; subst
      | _ => idtac
      end; now types_tac
    ].
Qed.

Lemma well_typed_binary_arithmetic_correct t1 aop t2 :
  boolSpec (well_typed_binary_arithmetic t1 aop t2) (D.wellTypedBinaryArithmetic t1 aop t2).
Proof.
  do 2 unfold_goal.
  unfold andb.
  repeat match goal with
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- integer    ?t = _ -> _ => case_fun (integer_correct    t)
  | _ => context_destruct
  end; solve [ constructor; assumption | inversion 1; types_tac].
Qed.

Lemma pointer_to_complete_object_correct t :
  if pointer_to_complete_object t
    then {q : qualifiers & {t' : ctype & (t = Pointer q t') * D.complete t'}}
    else neg (D.pointer t) + forall q t', t = Pointer q t' -> neg (D.complete t').
Proof.
  unfold_goal.
  repeat match goal with
  | [|- complete ?t = _ -> _] => case_fun (complete_correct t)
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => eexists; eexists; now intuition
  | _ => context_destruct
  end; right; congruence.
Qed.

Lemma pointers_to_compatible_complete_objects_correct t1 t2 :
  if pointers_to_compatible_complete_objects t1 t2
    then {q1' : qualifiers & {t1' : ctype &
         {q2' : qualifiers & {t2' : ctype &
           (t1 = Pointer q1' t1') * (t2 = Pointer q2' t2') *
           D.complete t1' * D.complete t2' * D.compatible t1' t2'}}}}
    else neg (D.pointer t1) + neg (D.pointer t2)
         + (forall q1' t1', t1 = Pointer q1' t1' -> neg (D.complete t1'))
         + (forall q2' t2', t2 = Pointer q2' t2' -> neg (D.complete t2'))
         + (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> neg (D.compatible t1' t2')).
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- complete ?t = _ -> _] => case_fun (complete_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => eexists; eexists; eexists; eexists; now intuition
  | [|- neg (D.pointer ?t) + _ + _ + _ + _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; left; left; left; inversion 1
      end
  | [|- _ + neg (D.pointer ?t) + _ + _ + _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; left; left; right; inversion 1
      end
  | [_ : neg (D.complete t1)      |- _ + _ + _ + _ + _ ] => left; left; right; intros; congruence
  | [_ : neg (D.complete t2)      |- _ + _ + _ + _ + _ ] => left; right; intros; congruence
  | [_ : neg (D.compatible t1 t2) |- _ + _ + _ + _ + _ ] => right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointers_to_compatible_objects_correct t1 t2 :
  if pointers_to_compatible_objects t1 t2
    then {q1' : qualifiers & {t1' : ctype &
         {q2' : qualifiers & {t2' : ctype &
           (t1 = Pointer q1' t1') * (t2 = Pointer q2' t2') *
           D.object t1'  * D.object t2' * D.compatible t1' t2'}}}}
    else neg (D.pointer t1) + neg (D.pointer t2)
         + (forall q1' t1', t1 = Pointer q1' t1' -> neg (D.object t1'))
         + (forall q2' t2', t2 = Pointer q2' t2' -> neg (D.object t2'))
         + (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> neg (D.compatible t1' t2')).
Proof.
  unfold_goal.
  unfold andb.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (object_correct t)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => eexists; eexists; eexists; eexists; intuition
  | [|- neg (D.pointer ?t) + _ + _ + _ + _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; left; left; left; inversion 1
      end
  | [|- _ + neg (D.pointer ?t) + _ + _ + _] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; left; left; right; inversion 1
      end
  | [_ : neg (D.object t1)      |- _ + _ + _ + _ + _ ] => left; left; right; intros; congruence
  | [_ : neg (D.object t2)      |- _ + _ + _ + _ + _ ] => left; right; intros; congruence
  | [_ : neg (D.compatible t1 t2) |- _ + _ + _ + _ + _ ] => right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma pointer_to_object_correct t :
  if pointer_to_object t
    then {q : qualifiers & {t' : ctype & (t = Pointer q t') * D.object t'}}
    else neg (D.pointer t) + forall q t', t = Pointer q t' -> neg (D.object t').
Proof.
  unfold_goal.
  repeat match goal with
  | [|- object ?t = _ -> _] => case_fun (object_correct t)
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => eexists; eexists; intuition
  | [|- neg (D.pointer ?t) + _] =>
      match t with
      | Pointer _ _ => right
      | _           => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointer_to_void_correct t :
  if pointer_to_void t
    then {q : qualifiers & {t' : ctype & (t = Pointer q t') * D.void t'}}
    else neg (D.pointer t) + forall q t', t = Pointer q t' -> neg (D.void t').
Proof.
  unfold_goal.
  repeat match goal with
  | [|- void ?t = _ -> _] => case_fun (void_correct t)
  | [|- neg _] => intros [? [? [? ?]]]
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => eexists; eexists; now intuition
  | [|- neg (D.pointer ?t) + _] =>
      match t with
      | Pointer _ _ => right; intros; inversion 1
      | _           => left; inversion 1
      end
  | _ => context_destruct
  end; congruence.
Qed.

Lemma pointers_to_compatible_types_correct t1 t2 :
  if pointers_to_compatible_types t1 t2
    then {q1' : qualifiers & {t1' : ctype &
         {q2' : qualifiers & {t2' : ctype &
           (t1 = Pointer q1' t1') * (t2 = Pointer q2' t2') *
           D.compatible t1' t2'}}}}
    else neg (D.pointer t1) + neg (D.pointer t2)
         + (forall q1' q2' t1' t2',
              t1 = Pointer q1' t1' ->
              t2 = Pointer q2' t2' -> neg (D.compatible t1' t2')).
Proof.
  unfold_goal.
  repeat match goal with
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- _ * _] => split
  | [|- {_ : _ & _}] => repeat eexists; now intuition 
  | [|- neg (D.pointer ?t) + _ + _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; left; inversion 1
      end
  | [|- _ + neg (D.pointer ?t) + _ ] =>
      match t with
      | Pointer _ _ => fail 1
      | _           => left; right; inversion 1
      end
  | [_ : neg (D.compatible t1 t2) |- _ + _ + _ ] => right; intros; congruence
  | _ => context_destruct
  end.
Qed.

Lemma well_typed_equality_correct {A B} {P} {G} {S : sigma A B} {e1 e2} {aop} {t1 t2} :
  (forall {t1 t1'}, D.typeOfRValue P G S e1 t1 -> D.typeOfRValue P G S e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P G S e2 t2 -> D.typeOfRValue P G S e2 t2' -> t2 = t2') ->
  D.typeOfRValue P G S e1 t1 ->
  D.typeOfRValue P G S e2 t2 ->
  (aop = Eq) + (aop = Ne) ->
  boolSpec (well_typed_equality t1 t2 (null_pointer_constant e1) (null_pointer_constant e2))
           (D.typeOfExpression' P G S (Binary e1 aop e2) (RValueType (Basic (Integer (Signed Int))))).
Proof.
  intros typeOfRValue_unique1 typeOfRValue_unique2 H1 H2 Haop.
  do 2 unfold_goal.
  unfold andb.
  unfold orb.
  repeat match goal with
  | [|- arithmetic ?t = _ -> _] => case_fun (arithmetic_correct t)
  | [|- pointer ?t = _ -> _] => case_fun (pointer_correct t)
  | [|- null_pointer_constant ?e = _ -> _] => case_fun (null_pointer_constant_correct e)
  | [|- pointer_to_complete_object ?t = _ -> _] => case_fun_tac (pointer_to_complete_object_correct t) autodestruct id_tac
  | [|- pointer_to_void ?t = _ -> _] => case_fun_tac (pointer_to_void_correct t) autodestruct id_tac
  | [|- pointer_to_object ?t = _ -> _] => case_fun_tac (pointer_to_object_correct t) autodestruct id_tac
  | [|- pointers_to_compatible_complete_objects ?t1 ?t2 = _ -> _] => case_fun_tac (pointers_to_compatible_complete_objects_correct t1 t2) autodestruct id_tac
  | [|- pointers_to_compatible_objects ?t1 ?t2 = _ -> _] => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | [|- pointers_to_compatible_types ?t1 ?t2 = _ -> _] => case_fun_tac (pointers_to_compatible_types_correct t1 t2) autodestruct id_tac
  | [|- compatible ?t1 ?t2 = ?o -> _] => case_fun (compatible_correct t1 t2)
  | _ => context_destruct
  | _ => destruct Haop; subst aop
  | [ H : D.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.complete _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [                      Hfalse : forall _ _, Pointer ?q1 Void = Pointer _ _ -> neg (D.void _)    |- False ] => now eapply (Hfalse q1 Void eq_refl D.Void_Void)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | |- D.typeOfExpression' P G S _ _ => types_tac; econstructor (finish eassumption)
  | H : _ + _ |- D.typeOfExpression' P G S _ _ => destruct H as [? | ?]
  end;
  abstract (
  match goal with
  | |- neg _ => inversion_clear 1
  end;
  repeat match goal with
  | [ H1 : D.typeOfRValue P G S e1 ?t1
    , H2 : D.typeOfRValue P G S e1 ?t2 |- _ ] => notSame t1 t2; pose proof (typeOfRValue_unique1 _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.typeOfRValue P G S e2 ?t1
    , H2 : D.typeOfRValue P G S e2 ?t2 |- _ ] => notSame t1 t2; pose proof (typeOfRValue_unique2 _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H : D.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.complete _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [                      Hfalse : forall _ _, Pointer ?q1 Void = Pointer _ _ -> neg (D.void _)    |- False ] => now eapply (Hfalse q1 Void eq_refl D.Void_Void)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H
  end).
Qed.

Lemma combine_qualifiers_left_not_pointer {t1 t2} :
  neg (D.pointer t2) -> combine_qualifiers_left t1 t2 = t1.
Proof.
  intros Hnpointer;
  destruct t1; destruct t2;
  solve [ reflexivity
        | exfalso; apply Hnpointer; constructor].
Qed.

Lemma combine_qualifiers_right_not_pointer {t1 t2} :
  neg (D.pointer t1) -> combine_qualifiers_right t1 t2 = t2.
Proof.
  intros Hnpointer;
  destruct t1; destruct t2;
  solve [ reflexivity
        | exfalso; apply Hnpointer; constructor].
Qed.

Lemma compatible_composite_None {t1} {t2} :
  D.compatible t1 t2 ->
  neg (composite t1 t2 = None).
Proof.
  apply (ctype_nrect (fun x => forall y (Hcompat : D.compatible x y), neg (composite x y = None))
                     (fun x => forall y (Hcompat : D.compatibleParams x y), neg (composite_params x y = None)));
  intros; unfold_goal;
  destruct y; simpl;
  unfold option_map; fold composite_params;
  inversion Hcompat; subst;
  repeat match goal with
  | |- eq_nat ?x ?y = _ -> _ => case_fun (eq_nat_correct x y)
  | |- eq_basicType ?x ?y = _ -> _ => case_fun (eq_basicType_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- composite _ _ = ?o -> _ => destruct o; intros ?
  | |- composite_params _ _ = ?o -> _ => destruct o; intros ?
  | _ => context_destruct
  end;
  intros;
  solve [ congruence
        | match goal with | IH : forall _ : ctype , _ |- _ => eapply IH; eassumption end
        | match goal with | IH : forall _ : list _, _ |- _ => eapply IH; eassumption end ].
Qed.

Lemma compatible_composite {t1} {t2} :
  D.compatible t1 t2 ->
  neg (forall t3, neg (D.composite t1 t2 t3)).
Proof.
  intros H.
  set (compatible_composite_None H).
  set (composite_correct t1 t2).
  optionSpec_destruct; firstorder.
Qed.

Lemma composite_pointer_correct t1 t2 :
  match composite_pointer t1 t2 with
  | Some t =>
      {q1' : qualifiers & {t1' : ctype &
      {q2' : qualifiers & {t2' : ctype & {
        t' : ctype &
            (t1 = Pointer  q1' t1')
          * (t2 = Pointer  q2' t2')
          * (t  = Pointer (combine_qualifiers q1' q2') t')
          * D.compatible t1' t2'
          * D.composite  t1' t2' t'
      }}}}}
  | None   => neg (D.pointer t1) +
              neg (D.pointer t2) +
              {q1' : qualifiers & {t1' : ctype &
              {q2' : qualifiers & {t2' : ctype &
                  (t1 = Pointer q1' t1')
                * (t2 = Pointer q2' t2')
                * neg (D.compatible t1' t2')
              }}}}
  end.
Proof.
  unfold_goal;
  unfold option_map.
  repeat match goal with
  | [|- composite ?t1 ?t2 = _ -> _] => case_fun (composite_correct t1 t2)
  | [|- compatible ?t1 ?t2 = _ -> _] => case_fun (compatible_correct t1 t2)
  | [|- neg _ + _ + _] => solve [ left; left ; inversion 1
                                | left; right; inversion 1
                                | repeat first [right | eexists | assumption]]
  | _ => context_destruct
  | [|- {_ : _ & _}] => repeat first [eexists | split | reflexivity | assumption]
  | [H : D.compatible ?t1 ?t2, Hfind : forall _, neg (D.composite ?t1 ?t2 _) |- _] => destruct (compatible_composite H Hfind)
  end.
Qed.

Lemma well_typed_conditional_correct_aux {A B} {P} {G} {S : sigma A B} {t1 t2 t3} {e1 e2 e3} :
  (forall {t1 t1'}, D.typeOfRValue P G S e1 t1 -> D.typeOfRValue P G S e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P G S e2 t2 -> D.typeOfRValue P G S e2 t2' -> t2 = t2') ->
  (forall {t3 t3'}, D.typeOfRValue P G S e3 t3 -> D.typeOfRValue P G S e3 t3' -> t3 = t3') ->
  D.typeOfRValue P G S e1 t1 ->
  D.typeOfRValue P G S e2 t2 ->
  D.typeOfRValue P G S e3 t3 ->
  optionSpec (well_typed_conditional P t1 t2 t3 (null_pointer_constant e2) (null_pointer_constant e3))
             (D.typeOfExpression' P G S (Conditional e1 e2 e3)).
Proof.
  intros typeOfRValue_functional1 typeOfRValue_functional2 typeOfRValue_functional3 ? ? ?.
  do 2 unfold_goal.
  destruct t1, t2, t3; simpl;
  unfold andb;
  unfold option_map;
  unfold combine_qualifiers_left;
  unfold combine_qualifiers_right;
  repeat match goal with
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | |- object ?t = _ -> _ => case_fun (object_correct t)
  | |- compatible ?t1 ?t2 = _ -> _ => case_fun (compatible_correct t1 t2)
  | |- composite ?t1 ?t2 = _ -> _ => case_fun (composite_correct t1 t2)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | |- void ?t = _ -> _ => case_fun (void_correct t)
  | |- pointer ?t = _ -> _ => case_fun (pointer_correct t)
  | |- null_pointer_constant ?e = _ -> _ => case_fun (null_pointer_constant_correct e)
  | |- pointer_to_object ?t = _ -> _ => case_fun_tac (pointer_to_object_correct t) autodestruct id_tac
  | |- pointer_to_void ?t = _ -> _ => case_fun_tac (pointer_to_void_correct t) autodestruct id_tac
  | |- composite_pointer ?t1 ?t2 = _ -> _ => case_fun_tac (composite_pointer_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = Some _ -> _ => intros ?; Tactics.subst_no_fail; Tactics.autoinjections
  | H : neg _ + neg _ + {_ : _ & {_ : _ & {_ : _ & {_ : _ & (_ = _) * (_ = _) * neg _}}}} |- D.typeOfExpression' P G S _ _ =>
      destruct H as [[H | H] | H];
      [ exfalso; apply H; constructor
      | exfalso; apply H; constructor
      | autodestruct H]
  | H : D.compatible ?t1 ?t2, Hfind : forall _, neg (D.composite ?t1 ?t2 _) |- _ => destruct (compatible_composite H Hfind)
  | |- D.typeOfExpression' P G S _ _ => 
        econstructor (
          solve [
              eassumption
            | constructor; apply usual_arithmetic_integer_correct
            | econstructor (eassumption)
            | finish fail
            | inversion 1; my_auto
            | repeat constructor])
  end;
  abstract (
  inversion 1; subst;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2 
  , H  : forall _ _, D.typeOfRValue P G S ?e _ -> _ -> _ = _ |- _ =>
      notSame t1 t2;
      pose proof (H _ _ H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | Hfalse : forall _ _, Pointer _ ?t   = Pointer _ _ -> neg (D.object _) , H : D.object ?t |- _ => destruct (Hfalse _ _ eq_refl H)
  | Hfalse : forall _ _, Pointer _ Void = Pointer _ _ -> neg (D.void   _) |- _ => exfalso; apply (Hfalse _ _ eq_refl); constructor
  | H  : D.usualArithmetic P ?t1 ?t2 _ , Hfalse : forall _, neg (D.usualArithmetic P ?t1 ?t2 _) |- _  => destruct (Hfalse _ H)
  | H1 : D.usualArithmetic P ?t1 ?t2 ?t, H2 : D.usualArithmetic P ?t1 ?t2 ?t' |- _ => notSame t t'; set (usualArithmetic_functional H1 H2)
  | _ => progress (repeat types_neg_tac)
  | H : _ + _ |- _ => destruct H
  end; my_auto; now firstorder).
Qed.

Lemma nullPointerConstant_typeOfExpression {A B} {P} {G} {S : sigma A B} :
  forall e,
  D.nullPointerConstant e ->
    D.typeOfExpression P G S e (RValueType (Basic (Integer (Signed Int))))
  + D.typeOfExpression P G S e (RValueType (Pointer no_qualifiers Void))
  + forall tc, neg (D.typeOfExpression P G S e tc).
Proof.
  apply (
    expression_nrect
      (fun e =>
         forall (Hnull : D.nullPointerConstant' e),
           D.typeOfExpression' P G S e (RValueType (Basic (Integer (Signed Int)))) +
           D.typeOfExpression' P G S e (RValueType (Pointer no_qualifiers Void))   +
           forall tc, neg (D.typeOfExpression' P G S e tc))
      (fun e =>
         forall (Hnull : D.nullPointerConstant  e),
           D.typeOfExpression  P G S e (RValueType (Basic (Integer (Signed Int)))) +
           D.typeOfExpression  P G S e (RValueType (Pointer no_qualifiers Void))   +
           forall tc, neg (D.typeOfExpression  P G S e tc))
      (fun _ => True));
  intros;
  first [now trivial | inversion_clear Hnull].
  - repeat match goal with
    | H : D.unqualified ?q |- _ => is_var q; inversion H; subst
    end.
    match goal with
    | IH : D.nullPointerConstant  ?e -> _, H : D.nullPointerConstant  ?e |- _ => destruct (IH H) as [[? | ?] |?]
    end.
    + left; right; econstructor (econstructor (solve [ eassumption
                                                     | reflexivity
                                                     | econstructor (constructor; constructor)
                                                     | econstructor (now repeat first [inversion 1 | constructor])])).
    + left; right; econstructor (econstructor (solve [ eassumption
                                                     | reflexivity
                                                     | econstructor (constructor; constructor)
                                                     | econstructor (now repeat first [inversion 1 | constructor])])).
    + right; inversion 1; subst.
      repeat match goal with
      | [Hfalse : forall _, neg (D.typeOfExpression P G S e _), H : D.typeOfExpression P G S e _ |- _] => exact (Hfalse _ H)
      | [H : D.typeOfRValue P G S _ _   |- _] => inversion_clear H
      | [H : D.typeOfLValue P G S _ _ _ |- _] => inversion_clear H
      end.
  - left; left; repeat constructor.
    + unfold_integer_range;
      eapply Implementation.integer_range_signed_upper;
      eapply Implementation.precision_ge_one.
    + unfold_integer_range;
      solve [eapply Implementation.integer_range_signed_lower1; eapply Implementation.precision_ge_one
            |eapply Implementation.integer_range_signed_lower2; eapply Implementation.precision_ge_one].
  - match goal with
    | IH : D.nullPointerConstant' ?e -> _, H : D.nullPointerConstant' ?e |- _ => destruct (IH H)  as [[? | ?] |?]
    end.
    + left ; left ; constructor; assumption.
    + left ; right; constructor; assumption.
    + right; inversion_clear 1; firstorder.
Qed.

Lemma nullPointerConstant_typeOfRValue {A B} {P} {G} {S : sigma A B} :
  forall e,
  D.nullPointerConstant e ->
    D.typeOfRValue P G S e (Basic (Integer (Signed Int)))
  + D.typeOfRValue P G S e (Pointer no_qualifiers Void)
  + forall t, neg (D.typeOfRValue P G S e t).
Proof.
  intros e Hnull.
  destruct (nullPointerConstant_typeOfExpression (P:=P) (G:=G) (S:=S) e Hnull) as [[? | ?] | ?].
  - left; left ; econstructor (solve [finish eassumption | constructor; inversion 1]).
  - left; right; econstructor (solve [finish eassumption | constructor; inversion 1]).
  - right; inversion_clear 1.
    + firstorder.
    + match goal with | H : D.typeOfLValue P G S e _ _ |- _ => inversion_clear H end.
      firstorder.
Qed.  

Lemma combine_qualifiers_unqualified_left {q} :
  combine_qualifiers no_qualifiers q = q.
Proof. destruct q; reflexivity. Qed.

Lemma combine_qualifiers_unqualified_right {q} :
  combine_qualifiers q no_qualifiers = q.
Proof.
  unfold no_qualifiers.
  unfold combine_qualifiers.
  destruct q.
  rewrite_all Bool.orb_false_r.
  reflexivity.
Qed.

Lemma typeOfExpression'_unique_functional {A B} {P} {G} {S : sigma A B} {e} :
  (optionUnique (type_of_expression' P G S e) (D.typeOfExpression' P G S e)) ->
  forall {tc tc'},
    D.typeOfExpression' P G S e tc  ->
    D.typeOfExpression' P G S e tc' ->
    tc = tc'.
Proof.
  intros type_of_expression'_unique ? ? H1 H2.
  set (type_of_expression'_unique _ H1).
  set (type_of_expression'_unique _ H2).
  congruence.
Qed.

Lemma typeOfExpression'_functional_conditional {A B} {P} {G} {S : sigma A B} {e1 e2 e3} :
  (forall {t1 t1'}, D.typeOfRValue P G S e1 t1 -> D.typeOfRValue P G S e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P G S e2 t2 -> D.typeOfRValue P G S e2 t2' -> t2 = t2') ->
  (forall {t3 t3'}, D.typeOfRValue P G S e3 t3 -> D.typeOfRValue P G S e3 t3' -> t3 = t3') ->
  forall {tc tc'}, D.typeOfExpression' P G S (Conditional e1 e2 e3) tc  ->
                   D.typeOfExpression' P G S (Conditional e1 e2 e3) tc' ->
                   tc = tc'.
Proof.
  intros Hunique1 Hunique2 Hunique3.
  inversion_clear 1; inversion_clear 1;
  repeat match goal with
  | [ Hunique : forall _ _, D.typeOfRValue P G S ?e _ -> D.typeOfRValue P G S ?e _ -> _ = _
    , H1 : D.typeOfRValue P G S ?e ?t1, H2 : D.typeOfRValue P G S ?e ?t2 |- _] => notSame t1 t2; pose proof (Hunique _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.usualArithmetic P ?t1 ?t2 ?t, H2 : D.usualArithmetic P ?t1 ?t2 ?t' |- _] => notSame t t'; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.composite ?t1 ?t2 ?t, H2 : D.composite ?t1 ?t2 ?t' |- _] => notSame t t'; pose proof (composite_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ Hunique : forall _ _, D.typeOfRValue P G S ?e _ -> D.typeOfRValue P G S ?e _ -> _ = _
    , Hnull : D.nullPointerConstant ?e
    , H : D.typeOfRValue P G S ?e (Pointer _ ?t) |- _] =>
      notSame t Void;
      let H' := fresh in
      destruct (@nullPointerConstant_typeOfRValue _ _ P G S e Hnull) as [[H' | H']| H'];
      [ discriminate (Hunique _ _ H H')
      | let Heq := fresh in set (Hunique _ _ H H') as Heq; inversion Heq; clear Heq; subst
      | destruct (H' _ H)]
  | _ => progress types_tac
  end.
Qed.

Lemma typeOfExpression'_neg_conditional1 {A B} {P} {G} {S : sigma A B} {e1 e2 e3} : 
  (forall t, neg (D.typeOfRValue P G S e1 t)) ->
  forall tc, neg (D.typeOfExpression' P G S (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Lemma typeOfExpression'_neg_conditional2 {A B} {P} {G} {S : sigma A B} {e1 e2 e3} : 
  (forall t, neg (D.typeOfRValue P G S e2 t)) ->
  forall tc, neg (D.typeOfExpression' P G S (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Lemma typeOfExpression'_neg_conditional3 {A B} {P} {G} {S : sigma A B} {e1 e2 e3} : 
  (forall t, neg (D.typeOfRValue P G S e3 t)) ->
  forall tc, neg (D.typeOfExpression' P G S (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Definition type_of_expression'_spec {A B} P G (S : sigma A B) e :=
  optionSpec   (type_of_expression' P G S e) (D.typeOfExpression' P G S e) *
  optionUnique (type_of_expression' P G S e) (D.typeOfExpression' P G S e).

Definition type_of_expression_spec {A B} P G (S : sigma A B) e :=
  optionSpec   (type_of_expression P G S e) (D.typeOfExpression P G S e) *
  optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e).

Definition well_typed_arguments_spec {A B} P G (S : sigma A B) es :=
  forall ps, boolSpec (well_typed_arguments P G S es ps) (D.typeOfArguments P G S es ps).

Definition type_of_expression'_correct_Constant {A B} {P} {G} {S : sigma A B} {c} :
  type_of_expression'_spec P G S (Constant c).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Constant c)).
  unfold_goal.
  unfold option_bind.
  destruct c; simpl.
  repeat match goal with
  | |- type_of_constant P ?ic = _ -> _ => case_fun (type_of_constant_correct P ic)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ * _ => split
  end;
  repeat match goal with
  | |- optionSpec (Some _) _ => now my_auto
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique _ _ => inversion_clear 1
  | H : forall _, neg _ |- False => eapply H; eassumption
  | H1 : D.typeOfConstant P ?ic ?it1 
  , H2 : D.typeOfConstant P ?ic ?it2 |- ?it1 = ?it2 => exact (typeOfConstant_functional H1 H2)
  | |- None = Some _ => exfalso
  | |- ?c _ = ?c _ => apply f_equal
  end.
Qed.

Lemma type_of_expression'_correct_Unary {A B} {P} {G} {S : sigma A B} {aop} {e} :
  type_of_expression_spec P G S e ->
  type_of_expression'_spec P G S (Unary aop e).
Proof.
  intros [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Unary aop e)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold option_bind.
  unfold option_map.
  unfold andb.
  unfold orb.
  destruct aop;
  repeat match goal with
  | |- type_of_rvalue P G S e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
  | |- type_of_expression P G S e = _ -> _ => case_fun Hcorrect
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- promotion P ?c = _ -> _ => case_fun (promotion_correct P c)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- real ?t = _ -> _ => case_fun (real_correct t)
  | |- pointer ?t = _ -> _ => case_fun (pointer_correct t)
  | |- complete ?t = _ -> _ => case_fun (complete_correct t)
  | |- object ?t = _ -> _ => case_fun (object_correct t)
  | |- unqualified ?q = _ -> _ => case_fun (unqualified_correct q)
  | |- modifiable ?q ?t = _ -> _ => case_fun (modifiable_correct q t)
  | |- lvalue_conversion ?t = _ -> _ => case_fun (lvalue_conversion_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  abstract (
  repeat match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique _ _ => inversion_clear 1
  | H : forall _, neg _ |- False => eapply H; eassumption
  | |- None = Some _ => exfalso
  | |- ?c _ = ?c _ => apply f_equal
  | H : D.typeOfLValue P G S _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1 
  , H2 : D.typeOfRValue P G S ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux Hunique H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.promotion P ?t ?t1 
  , H2 : D.promotion P ?t ?t2 |- _ => notSame t1 t2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.typeOfExpression P G S ?e ?t1 
  , H2 : D.typeOfExpression P G S ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux Hunique H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.lvalueConversion ?t ?t1 
  , H2 : D.lvalueConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (lvalueConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | |- _ => finish fail
  | _ => progress types_tac
  end).
Qed.

Lemma type_of_expression'_correct_Binary_Comma {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Comma e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Comma e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold option_bind.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec (Some _) _ => now my_auto
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1 
  , H2 : D.typeOfRValue P G S ?e ?t2 |- ?t1 = ?t2 => eapply typeOfRValue_functional_aux; eassumption
  | H : forall _, neg _ |- False => eapply H; eassumption
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Mul {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Mul) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Mul) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1 
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Div {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Div) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Div) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1 
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1 
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Mod {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Mod) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Mod) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => progress types_tac
  end.
Qed.

Definition type_of_expression'_correct_Binary_Arithmetic_Add {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Add) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Add) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | |- pointer_to_complete_object ?t = _ -> _ => case_fun_tac (pointer_to_complete_object_correct t) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  abstract (
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | [ H : D.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.complete _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end).
Qed.

Definition type_of_expression'_correct_Binary_Arithmetic_Sub {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Sub) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Sub) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | |- pointer_to_complete_object ?t = _ -> _ => case_fun_tac (pointer_to_complete_object_correct t) autodestruct id_tac
  | |- pointers_to_compatible_complete_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_complete_objects_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  abstract (
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.usualArithmetic P ?t ?t' ?t1
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | H : D.wellTypedBinaryArithmetic (Pointer _ _) _ _ |- _ => inversion_clear H
  | H : D.wellTypedBinaryArithmetic _ _ (Pointer _ _) |- _ => inversion_clear H
  | [ H : D.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.complete _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end).
Qed.

Definition type_of_expression'_correct_Binary_Arithmetic_Shl {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Shl) e2).
Proof. 
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Shl) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- promotion P ?t = _ -> _ => case_fun (promotion_correct P t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.promotion P ?t ?t1 
  , H2 : D.promotion P ?t ?t2 |- _ => notSame t1 t2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Arithmetic_Shr {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Shr) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Shr) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- promotion P ?t = _ -> _ => case_fun (promotion_correct P t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.promotion P ?t ?t1 
  , H2 : D.promotion P ?t ?t2 |- _ => notSame t1 t2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Band {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Band) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Band) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.usualArithmetic P ?t ?t' ?t1 
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Bor {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Bor) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Bor) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.usualArithmetic P ?t ?t' ?t1 
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Xor {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 (Arithmetic Xor) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 (Arithmetic Xor) e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- usual_arithmetic P ?t1 ?t2 = _ -> _ => case_fun (usual_arithmetic_correct P t1 t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.usualArithmetic P ?t ?t' ?t1 
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_And {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 And e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 And e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Or {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Or e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Or e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Lt {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Lt e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Lt e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- real ?t = _ -> _ => case_fun (real_correct t)
  | |- pointers_to_compatible_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Gt {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Gt e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Gt e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- real ?t = _ -> _ => case_fun (real_correct t)
  | |- pointers_to_compatible_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Le {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Le e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Le e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- real ?t = _ -> _ => case_fun (real_correct t)
  | |- pointers_to_compatible_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Ge {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Ge e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Ge e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- real ?t = _ -> _ => case_fun (real_correct t)
  | |- pointers_to_compatible_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | [ H : D.object   ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.object   _) |- False ] => now eapply (Hfalse q1 t1 eq_refl H)
  | [ Hfalse : forall _ _ _ _, Pointer ?q1 ?t1 = _ ->
                               Pointer ?q2 ?t2 = _ ->
                               neg (D.compatible _ _)
  , H : D.compatible ?t1 ?t2 |- False] => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Eq {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Eq e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Eq e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | H1 : D.typeOfRValue P G S e1 _ , H2 : D.typeOfRValue P G S e2 _ |- well_typed_equality ?t1 ?t2 (null_pointer_constant ?e1) (null_pointer_constant ?e2)  = _ -> _ =>
      case_fun (well_typed_equality_correct
              (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique1)
              (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique2) H1 H2 (inl (eq_refl Eq)))
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => assumption
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H2 : neg (D.typeOfExpression' P G S (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))))) |- False => apply H2; econstructor (eassumption)
  | _ => finish fail
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Ne {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Binary e1 Ne e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Binary e1 Ne e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | H1 : D.typeOfRValue P G S e1 _ , H2 : D.typeOfRValue P G S e2 _ |- well_typed_equality ?t1 ?t2 (null_pointer_constant ?e1) (null_pointer_constant ?e2)  = _ -> _ =>
      case_fun (well_typed_equality_correct
              (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique1)
              (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique2) H1 H2 (inr (eq_refl Ne)))
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => assumption
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H2 : neg (D.typeOfExpression' P G S (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))))) |- False => apply H2; econstructor (eassumption)
  | _ => finish fail
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Assign {A B} {P} {G} {S : sigma A B} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (Assign e1 e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Assign e1 e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  fold (@assignable A B P G S).
  unfold andb.
  repeat match goal with
  | |- type_of_expression P G S e1 = _ -> _ => case_fun Hcorrect1
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- assignable P G S (pointer_conversion ?t) e2 = _ -> _ => pose proof (pointer_conversion_correct t); case_fun (assignable_correct_aux (t1:=pointer_conversion t) Hcorrect2 Hunique2)
  | |- modifiable ?q ?t = _ -> _ => case_fun (modifiable_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H : D.typeOfLValue P G S _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.typeOfExpression P G S ?e ?t1
  , H2 : D.typeOfExpression P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : findSpec ?t1 (D.pointerConversion ?t)
  , H2 : D.pointerConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (pointerConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : forall _, neg (D.typeOfRValue P G S ?e _), H : D.assignable P G S _ ?e |- False => inversion_clear H
  | _ => reflexivity
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_CompoundAssign {A B} {P} {G} {S : sigma A B} {aop} {e1 e2} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression'_spec P G S (CompoundAssign e1 aop e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (CompoundAssign e1 aop e2)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold option_bind.
  unfold andb.
  unfold orb.
  repeat match goal with
  | |- type_of_expression P G S e1 = _ -> _ => case_fun Hcorrect1
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- modifiable ?q ?t = _ -> _ => case_fun (modifiable_correct q t)
  | |- arithmetic ?t = _ -> _ => case_fun (arithmetic_correct t)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- lvalue_conversion ?t = _ -> _ => case_fun (lvalue_conversion_correct t)
  | |- pointer_to_complete_object ?t = _ -> _ => case_fun_tac (pointer_to_complete_object_correct t) autodestruct id_tac
  | |- well_typed_binary_arithmetic ?t1 ?aop ?t2 = _ -> _ => case_fun (well_typed_binary_arithmetic_correct t1 aop t2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  abstract (
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H : D.typeOfLValue P G S _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.typeOfExpression P G S ?e ?t1
  , H2 : D.typeOfExpression P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.lvalueConversion ?t ?t1 
  , H2 : D.lvalueConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (lvalueConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H : D.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> neg (D.complete _) |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | _ : neg (D.integer ?t), H : D.arithmetic ?t |- False => inversion_clear H
  | _ : neg (D.integer ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H
  | _ : neg (D.integer ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end).
Qed.

Definition type_of_expression'_correct_Conditional {A B} {P} {G} {S : sigma A B} {e1 e2 e3} :
  type_of_expression_spec P G S e1 ->
  type_of_expression_spec P G S e2 ->
  type_of_expression_spec P G S e3 ->
  type_of_expression'_spec P G S (Conditional e1 e2 e3).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2] [Hcorrect3 Hunique3].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Conditional e1 e2 e3)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold option_bind.
  repeat match goal with
  | |- type_of_rvalue P G S e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P G S e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- type_of_rvalue P G S e3 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect3 Hunique3)
  | H1 : D.typeOfRValue P G S e1 _
  , H2 : D.typeOfRValue P G S e2 _
  , H3 : D.typeOfRValue P G S e3 _
    |- well_typed_conditional P _ _ _ (null_pointer_constant e2) (null_pointer_constant e3) = _ -> _ =>
      case_fun (well_typed_conditional_correct_aux
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique1)
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique2)
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique3)
                  H1 H2 H3)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec _ _ => assumption
  | H1 : D.typeOfExpression' P G S (Conditional _ _ _) _ |- optionUnique (Some _) _ =>
      let H2 := fresh in
      intros ? H2;
      apply f_equal;
      exact (typeOfExpression'_functional_conditional
               (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique1)
               (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique2)
               (@typeOfRValue_functional_aux _ _ _ _ _ _ Hunique3) H1 H2)
  | H1 : forall _, neg (D.typeOfExpression' P G S (Conditional _ _ _) _) |- optionUnique None _ =>
      let H2 := fresh in
      intros ? H2; destruct (H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P G S e1 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional1 H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P G S e2 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional2 H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P G S e3 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional3 H1 _ H2)
  end.
Qed.

Definition type_of_expression'_correct_Cast {A B} {P} {G} {S : sigma A B} {q} {t} {e} :
  type_of_expression_spec P G S e ->
  type_of_expression'_spec P G S (Cast q t e).
Proof.
  intros [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Cast q t e)); simpl.
  fold (@type_of_rvalue A B P G S).
  unfold andb.
  repeat match goal with
  | |- type_of_rvalue P G S e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
  | |- wf_lvalue ?q ?t = _ -> _ => case_fun (wf_lvalue_correct q t)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => reflexivity
  end.
Qed.

Definition type_of_expression'_correct_Call {A B} {P} {G} {S : sigma A B} {e} {es} :
  well_typed_arguments_spec P G S es ->
  type_of_expression_spec P G S e ->
  type_of_expression'_spec P G S (Call e es).
Proof.
  intros Hargs [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Call e es)); simpl.
  fold (@type_of_rvalue A B P G S).
  fold (@assignable A B P G S).
  fold (@well_typed_arguments A B P G S).
  unfold andb.
  repeat match goal with
  | |- type_of_rvalue P G S e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
  | |- well_typed_arguments P G S ?es ?ps = _ -> _ => case_fun (Hargs ps)
  | |- unqualified ?q = _ -> _ => case_fun (unqualified_correct q)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P G S ?e ?t1
  , H2 : D.typeOfRValue P G S ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P G S ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Definition type_of_expression'_correct_Var {A B} {P} {G} {S : sigma A B} {v} :
  D.disjoint G S ->
  type_of_expression'_spec P G S (Var v).
Proof.
  intros Hdisjoint.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (Var v)); simpl.
  repeat match goal with
  | |- lookup ?C v = _ -> _ => case_fun (lookup_correct C v)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.lookup ?C ?v ?r1
  , H2 : D.lookup ?C ?v ?r2 |- _ => notSame r1 r2; pose proof (lookup_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | HG : D.lookup G ?v _
  , HS : D.lookup S ?v _ |- _ => exfalso; eapply Hdisjoint; eexists; eassumption
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => reflexivity
  end.
Qed.

Definition type_of_expression'_correct_SizeOf {A B} {P} {G} {S : sigma A B} {q} {t} :
  type_of_expression'_spec P G S (SizeOf q t).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (SizeOf q t)); simpl.
  unfold andb.
  unfold negb.
  repeat match goal with
  | |- function ?t = _ -> _ => case_fun (function_correct t)
  | |- incomplete ?t = _ -> _ => case_fun (incomplete_correct t)
  | |- wf_lvalue ?q ?t = _ -> _ => case_fun (wf_lvalue_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => congruence
  end.
Qed.

Definition type_of_expression'_correct_AlignOf {A B} {P} {G} {S : sigma A B} {q} {t} :
  type_of_expression'_spec P G S (AlignOf q t).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P G S (AlignOf q t)); simpl.
  unfold andb.
  unfold negb.
  repeat match goal with
  | |- function ?t = _ -> _ => case_fun (function_correct t)
  | |- incomplete ?t = _ -> _ => case_fun (incomplete_correct t)
  | |- wf_lvalue ?q ?t = _ -> _ => case_fun (wf_lvalue_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- optionSpec (Some _) _ => econstructor (finish eassumption)
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => congruence
  end.
Qed.

Definition well_typed_arguments_correct_nil {A B} {P} {G} {S : sigma A B} :
  well_typed_arguments_spec P G S nil.
Proof.
  destruct ps; simpl.
  - constructor.
  - inversion 1.
Qed.

Definition well_typed_arguments_correct_cons {A B} {P} {G} {S : sigma A B} {e} {es} :
  type_of_expression_spec P G S e ->
  well_typed_arguments_spec P G S es ->
  well_typed_arguments_spec P G S (e :: es).
Proof.
  intros [Hcorrect Hunique] Hargs ps.
  pull_out bool (well_typed_arguments P G S (e :: es) ps); simpl.
  unfold andb.
  repeat match goal with
  | |- assignable P G S (pointer_conversion ?t) e = _ -> _ => pose proof (pointer_conversion_correct t); case_fun (assignable_correct_aux (t1:=pointer_conversion t) Hcorrect Hunique)
  | |- well_typed_arguments P G S ?es ?ps = _ -> _ => case_fun (Hargs ps)
  | _ => context_destruct
  | |- true  = ?v -> _ => is_var v; intros ?; subst
  | |- false = ?v -> _ => is_var v; intros ?; subst
  | |- boolSpec true _ => econstructor (eassumption)
  end;
  match goal with
  | |- boolSpec false _ => inversion_clear 1
  end;
  repeat match goal with
  | H1 : findSpec ?t1 (D.pointerConversion ?t)
  , H2 : D.pointerConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (pointerConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  end.
Qed.

Definition type_of_expression_correct_AnnotatedExpression {A B} {P} {G} {S : sigma A B} {a} {e} :
  type_of_expression'_spec P G S e ->
  type_of_expression_spec P G S (AnnotatedExpression a e).
Proof.
  intros [Hcorrect Hunique].
  unfold type_of_expression_spec; simpl.
  optionSpec_destruct; split;
  match goal with
  | |- optionSpec (Some _) _ => constructor; assumption
  | |- optionSpec None _ => inversion_clear 1
  | |- optionUnique (Some _) _ => inversion_clear 1; repeat apply f_equal
  | |- optionUnique None _ => inversion_clear 1; exfalso
  end;
  repeat match goal with
  | H1 : D.typeOfExpression' P G S ?e ?t1
  , H  : optionUnique (Some ?t2) (D.typeOfExpression' P G S ?e) |- _ => notSame t1 t2; pose proof (H _ H1); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  end; reflexivity.
Qed.

Definition type_of_expression_correct_unique {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, type_of_expression_spec P G S e.
Proof.
  intros Hdisjoint.
  eapply (expression_nrect (fun e => type_of_expression'_spec P G S e)
                           (fun e => type_of_expression_spec  P G S e)
                           (fun es => well_typed_arguments_spec P G S es));
  intros.
  apply type_of_expression'_correct_Unary; assumption.
  destruct bop.
  destruct aop.
  apply type_of_expression'_correct_Binary_Arithmetic_Mul; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Div; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Mod; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Add; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Sub; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Shl; assumption.
  apply type_of_expression'_correct_Binary_Arithmetic_Shr; assumption.
  apply type_of_expression'_correct_Binary_Band; assumption.
  apply type_of_expression'_correct_Binary_Bor; assumption.
  apply type_of_expression'_correct_Binary_Xor; assumption.
  apply type_of_expression'_correct_Binary_Comma; assumption.
  apply type_of_expression'_correct_Binary_And; assumption.
  apply type_of_expression'_correct_Binary_Or; assumption.
  apply type_of_expression'_correct_Binary_Lt; assumption.
  apply type_of_expression'_correct_Binary_Gt; assumption.
  apply type_of_expression'_correct_Binary_Le; assumption.
  apply type_of_expression'_correct_Binary_Ge; assumption.
  apply type_of_expression'_correct_Binary_Eq; assumption.
  apply type_of_expression'_correct_Binary_Ne; assumption.
  apply type_of_expression'_correct_Assign; assumption.
  apply type_of_expression'_correct_CompoundAssign; assumption.
  apply type_of_expression'_correct_Conditional; assumption.
  apply type_of_expression'_correct_Cast; assumption.
  apply type_of_expression'_correct_Call; assumption.
  apply type_of_expression'_correct_Constant; assumption.
  apply type_of_expression'_correct_Var; assumption.
  apply type_of_expression'_correct_SizeOf; assumption.
  apply type_of_expression'_correct_AlignOf; assumption.
  apply well_typed_arguments_correct_nil; assumption.
  apply well_typed_arguments_correct_cons; assumption.
  apply type_of_expression_correct_AnnotatedExpression; assumption.
Qed.

Definition type_of_expression_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, optionSpec (type_of_expression P G S e) (D.typeOfExpression P G S e).
Proof.
  intros Hdisjoint e.
  destruct (type_of_expression_correct_unique P G S Hdisjoint e) as [? _].
  assumption.
Qed.

Definition type_of_expression_unique {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, optionUnique (type_of_expression P G S e) (D.typeOfExpression P G S e).
Proof.
  intros Hdisjoint e.
  destruct (type_of_expression_correct_unique P G S Hdisjoint e) as [_ ?].
  assumption.
Qed.

Lemma typeOfExpression_functional {A B} {P} {G} {S : sigma A B} {e} (Hdisjoint : D.disjoint G S) :
  forall {tc1 tc2},
    D.typeOfExpression P G S e tc1 ->
    D.typeOfExpression P G S e tc2 ->
    tc1 = tc2.
Proof.
  intros ? ? H1 H2.
  set (type_of_expression_unique P G S Hdisjoint e _ H1).
  set (type_of_expression_unique P G S Hdisjoint e _ H2).
  congruence.
Qed.
Arguments typeOfExpression_functional : default implicits.

Lemma typeable_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, boolSpec (typeable P G S e) (D.typeable P G S e).
Proof.
  intros Hdisjoint e.
  unfold typeable.
  pose proof (type_of_expression_correct P G S Hdisjoint e).
  optionSpec_destruct; simpl.
  - econstructor; eassumption.
  - inversion_clear 1; firstorder.
Qed.

Definition type_of_rvalue_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, optionSpec (type_of_rvalue P G S e) (D.typeOfRValue P G S e).
Proof.
  intros Hdisjoint e.
  apply type_of_rvalue_correct_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.

Definition type_of_rvalue_unique {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall e, optionUnique (type_of_rvalue P G S e) (D.typeOfRValue P G S e).
Proof.
  intros Hdisjoint e.
  apply type_of_rvalue_unique_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.

Lemma typeOfRValue_functional {A B} {P} {G} {S : sigma A B} (Hdisjoint : D.disjoint G S) :
  forall e {t1 t2},
    D.typeOfRValue P G S e t1 ->
    D.typeOfRValue P G S e t2 ->
    t1 = t2.
Proof.
  intros e ? ? H1 H2.
  set (type_of_rvalue_unique P G S Hdisjoint e _ H1).
  set (type_of_rvalue_unique P G S Hdisjoint e _ H2).
  congruence.
Qed.

Lemma assignable_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall t1 e2, boolSpec (assignable P G S t1 e2) (D.assignable P G S t1 e2).
Proof.
  intros Hdisjoint t1 e2.
  apply assignable_correct_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.
