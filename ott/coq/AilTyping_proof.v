Require Program.Tactics.

Require Import Common.
Require Import Context.
Require Import AilTypes.
Require Import AilSyntax.
Require Import AilSyntaxAux.
Require Import AilTypesAux.
Require Import AilWf.
Require Import AilTyping.

Require Import Context_proof.
Require Import AilTypes_proof.
Require Import AilSyntax_proof.
Require Import AilSyntaxAux_proof.
Require Import AilWf_proof.
Require Import AilTypesAux_proof.

Module D.
  Require AilTyping_defns.

  Include Context_defns.
  Include AilSyntax_defns.
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

Lemma typeOfExpression_sub {A B1 B2} {P} {S : sigma B1 B2} {G1 G2 : gamma} {e : expression A} :
  D.subP (fun v => D.fv v e) eq G1 G2 ->
  forall t,
    D.typeOfExpression P S G1 e t ->
    D.typeOfExpression P S G2 e t.
Proof.
  apply (
    expression_nrect
      (fun x => forall (Hfree : D.subP (fun v => D.fv'         v x) eq G1 G2) t (T1 : D.typeOfExpression' P S G1 x t), D.typeOfExpression' P S G2 x t)
      (fun x => forall (Hfree : D.subP (fun v => D.fv          v x) eq G1 G2) t (T1 : D.typeOfExpression  P S G1 x t), D.typeOfExpression  P S G2 x t)
      (fun x => forall (Hfree : D.subP (fun v => D.fvArguments v x) eq G1 G2) t (T1 : D.typeOfArguments   P S G1 x t), D.typeOfArguments   P S G2 x t)
  ); intros; inversion_clear T1;
  match goal with
  | H : D.assignable   P S G1 _ _   |- _ => inversion H; subst
  | _ => idtac
  end;
  repeat match goal with
  | H : D.typeOfLValue P S G1 _ _ _ |- _ => inversion_clear H
  | H : D.typeOfRValue P S G1 _ _   |- _ => inversion_clear H
  | H : D.typeOfExpression _ _ G1 ?e _, IH : D.subP (fun _ => D.fv _ ?e) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fv v e) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fv v e) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.typeOfExpression' _ _ G1 ?e _, IH : D.subP (fun _ => D.fv' _ ?e) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fv' v e) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fv' v e) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.typeOfArguments _ _ G1 ?es _, IH : D.subP (fun _ => D.fvArguments _ ?es) _ _ _ -> _ |- _ =>
      notHyp (D.subP (fun v => D.fvArguments v es) eq G1 G2);
      let Hfree_sub := fresh in
      assert (D.subP (fun v => D.fvArguments v es) eq G1 G2) as Hfree_sub
        by (intros ? ?; apply Hfree; solve [econstructor (eassumption) | assumption]);
      set (IH Hfree_sub _ H)
  | H : D.lookup G1 ?v _ |- D.typeOfExpression' _ _ G2 (Var ?v) _ =>
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

Lemma type_of_rvalue_correct_aux {A B1 B2} {P} {G} {S : sigma B1 B2} {e : expression A} :
  optionSpec   (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  optionSpec   (type_of_rvalue P S G e) (D.typeOfRValue P S G e).
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
      | H : D.typeOfLValue     P S G _ _ _ |- _ => inversion_clear H
      | H : D.typeOfExpression P S G _ _   |- _ =>
          let Heq := fresh in
          set (type_of_expression_unique _ H) as Hfresh;
          congruence || Tactics.autoinjections; now firstorder
      end
    ].
Qed.

Lemma type_of_rvalue_unique_aux {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} :
  optionSpec   (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  optionUnique (type_of_rvalue P S G e) (D.typeOfRValue P S G e).
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
  | H : D.typeOfLValue     P S G _ _ _ |- _ => inversion_clear H
  | H : D.typeOfRValue     P S G _ _   |- _ => inversion_clear H
  | H : D.typeOfExpression P S G _ _   |- _ =>
      let Heq := fresh in
      set (type_of_expression_unique _ H) as Hfresh;
      discriminate Hfresh || Tactics.autoinjections
  end;
  solve [ apply f_equal; eapply (lvalueConversion_functional ); eassumption
        | apply f_equal; eapply (pointerConversion_functional); eassumption
        | now firstorder ].
Qed.

Lemma typeOfExpression_functional_aux {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} :
  optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  forall {tc tc'},
    D.typeOfExpression P S G e tc  ->
    D.typeOfExpression P S G e tc' ->
    tc = tc'.
Proof.
  intros type_of_expression_unique ? ? H1 H2.
  set (type_of_expression_unique _ H1).
  set (type_of_expression_unique _ H2).
  congruence.
Qed.

Lemma typeOfRValue_functional_aux {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} :
  optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e) ->
  forall {t t'},
    D.typeOfRValue P S G e t  ->
    D.typeOfRValue P S G e t' ->
    t = t'.
Proof.
  intros type_of_expression_unique.
  inversion_clear 1; inversion_clear 1;
  repeat match goal with
  | H : D.typeOfLValue P S G _ _ _ |- _ => inversion_clear H
  end;
  match goal with
  | H1 : D.typeOfExpression P S G ?e _
  , H2 : D.typeOfExpression P S G ?e _ |- _ =>
      let Heq := fresh in
      set (typeOfExpression_functional_aux type_of_expression_unique H1 H2) as Heq;
      discriminate Heq || Tactics.autoinjections
  end;
  solve [
      eapply pointerConversion_functional; eassumption
    | eapply lvalueConversion_functional ; eassumption ].
Qed.

Lemma type_of_rvalue_lvalue_eq {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} {q1} {t1 t2} :
  type_of_expression P S G e = Some (LValueType q1 t1) ->
  type_of_rvalue P S G e = Some t2 ->
  t1 = t2.
Proof.
  intros Heq.
  do 2 unfold_goal.
  rewrite Heq.
  destruct t1; my_auto.
Qed.

Lemma type_of_rvalue_aux_lvalue_eq_lift {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} {q1} {t1 t2}:
  D.typeOfExpression P S G e (LValueType q1 t1) ->
  type_of_expression P S G e = Some (LValueType q1 t1) ->
  type_of_rvalue P S G e = Some t2 ->
  D.typeOfRValue P S G e t1.
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

Lemma assignable_correct_aux {A B1 B2} {P} {S : sigma B1 B2} {G} {t1} {e2 : expression A} :
  optionSpec   (type_of_expression P S G e2) (D.typeOfExpression P S G e2) ->
  optionUnique (type_of_expression P S G e2) (D.typeOfExpression P S G e2) ->
  boolSpec (assignable P S G t1 e2) (D.assignable P S G t1 e2).
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
      | H : D.typeOfRValue P S G e2 _ |- _ =>
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

Lemma well_typed_equality_correct {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} {aop} {t1 t2} :
  (forall {t1 t1'}, D.typeOfRValue P S G e1 t1 -> D.typeOfRValue P S G e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P S G e2 t2 -> D.typeOfRValue P S G e2 t2' -> t2 = t2') ->
  D.typeOfRValue P S G e1 t1 ->
  D.typeOfRValue P S G e2 t2 ->
  (aop = Eq) + (aop = Ne) ->
  boolSpec (well_typed_equality t1 t2 (null_pointer_constant e1) (null_pointer_constant e2))
           (D.typeOfExpression' P S G (Binary e1 aop e2) (RValueType (Basic (Integer (Signed Int))))).
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
  | |- D.typeOfExpression' P S G _ _ => types_tac; econstructor (finish eassumption)
  | H : _ + _ |- D.typeOfExpression' P S G _ _ => destruct H as [? | ?]
  end;
  abstract (
  match goal with
  | |- neg _ => inversion_clear 1
  end;
  repeat match goal with
  | [ H1 : D.typeOfRValue P S G e1 ?t1
    , H2 : D.typeOfRValue P S G e1 ?t2 |- _ ] => notSame t1 t2; pose proof (typeOfRValue_unique1 _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.typeOfRValue P S G e2 ?t1
    , H2 : D.typeOfRValue P S G e2 ?t2 |- _ ] => notSame t1 t2; pose proof (typeOfRValue_unique2 _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
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

Lemma well_typed_conditional_correct_aux {A B1 B2} {P} {S : sigma B1 B2} {G} {t1 t2 t3} {e1 e2 e3 : expression A} :
  (forall {t1 t1'}, D.typeOfRValue P S G e1 t1 -> D.typeOfRValue P S G e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P S G e2 t2 -> D.typeOfRValue P S G e2 t2' -> t2 = t2') ->
  (forall {t3 t3'}, D.typeOfRValue P S G e3 t3 -> D.typeOfRValue P S G e3 t3' -> t3 = t3') ->
  D.typeOfRValue P S G e1 t1 ->
  D.typeOfRValue P S G e2 t2 ->
  D.typeOfRValue P S G e3 t3 ->
  optionSpec (well_typed_conditional P t1 t2 t3 (null_pointer_constant e2) (null_pointer_constant e3))
             (D.typeOfExpression' P S G (Conditional e1 e2 e3)).
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
  | H : neg _ + neg _ + {_ : _ & {_ : _ & {_ : _ & {_ : _ & (_ = _) * (_ = _) * neg _}}}} |- D.typeOfExpression' P S G _ _ =>
      destruct H as [[H | H] | H];
      [ exfalso; apply H; constructor
      | exfalso; apply H; constructor
      | autodestruct H]
  | H : D.compatible ?t1 ?t2, Hfind : forall _, neg (D.composite ?t1 ?t2 _) |- _ => destruct (compatible_composite H Hfind)
  | |- D.typeOfExpression' P S G _ _ => 
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2 
  , H  : forall _ _, D.typeOfRValue P S G ?e _ -> _ -> _ = _ |- _ =>
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

Lemma nullPointerConstant_typeOfExpression {A B1 B2} {P} {S : sigma B1 B2} {G} :
  forall e : expression A,
  D.nullPointerConstant e ->
    D.typeOfExpression P S G e (RValueType (Basic (Integer (Signed Int))))
  + D.typeOfExpression P S G e (RValueType (Pointer no_qualifiers Void))
  + forall tc, neg (D.typeOfExpression P S G e tc).
Proof.
  apply (
    expression_nrect
      (fun e =>
         forall (Hnull : D.nullPointerConstant' e),
           D.typeOfExpression' P S G e (RValueType (Basic (Integer (Signed Int)))) +
           D.typeOfExpression' P S G e (RValueType (Pointer no_qualifiers Void))   +
           forall tc, neg (D.typeOfExpression' P S G e tc))
      (fun e =>
         forall (Hnull : D.nullPointerConstant  e),
           D.typeOfExpression  P S G e (RValueType (Basic (Integer (Signed Int)))) +
           D.typeOfExpression  P S G e (RValueType (Pointer no_qualifiers Void))   +
           forall tc, neg (D.typeOfExpression  P S G e tc))
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
      | [Hfalse : forall _, neg (D.typeOfExpression P S G e _), H : D.typeOfExpression P S G e _ |- _] => exact (Hfalse _ H)
      | [H : D.typeOfRValue P S G _ _   |- _] => inversion_clear H
      | [H : D.typeOfLValue P S G _ _ _ |- _] => inversion_clear H
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

Lemma nullPointerConstant_typeOfRValue {A B1 B2} {P} {S : sigma B1 B2} {G} :
  forall e : expression A,
  D.nullPointerConstant e ->
    D.typeOfRValue P S G e (Basic (Integer (Signed Int)))
  + D.typeOfRValue P S G e (Pointer no_qualifiers Void)
  + forall t, neg (D.typeOfRValue P S G e t).
Proof.
  intros e Hnull.
  destruct (nullPointerConstant_typeOfExpression (P:=P) (G:=G) (S:=S) e Hnull) as [[? | ?] | ?].
  - left; left ; econstructor (solve [finish eassumption | constructor; inversion 1]).
  - left; right; econstructor (solve [finish eassumption | constructor; inversion 1]).
  - right; inversion_clear 1.
    + firstorder.
    + match goal with | H : D.typeOfLValue P S G e _ _ |- _ => inversion_clear H end.
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

Lemma typeOfExpression'_unique_functional {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression' A} :
  (optionUnique (type_of_expression' P S G e) (D.typeOfExpression' P S G e)) ->
  forall {tc tc'},
    D.typeOfExpression' P S G e tc  ->
    D.typeOfExpression' P S G e tc' ->
    tc = tc'.
Proof.
  intros type_of_expression'_unique ? ? H1 H2.
  set (type_of_expression'_unique _ H1).
  set (type_of_expression'_unique _ H2).
  congruence.
Qed.

Lemma typeOfExpression'_functional_conditional {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A} :
  (forall {t1 t1'}, D.typeOfRValue P S G e1 t1 -> D.typeOfRValue P S G e1 t1' -> t1 = t1') ->
  (forall {t2 t2'}, D.typeOfRValue P S G e2 t2 -> D.typeOfRValue P S G e2 t2' -> t2 = t2') ->
  (forall {t3 t3'}, D.typeOfRValue P S G e3 t3 -> D.typeOfRValue P S G e3 t3' -> t3 = t3') ->
  forall {tc tc'}, D.typeOfExpression' P S G (Conditional e1 e2 e3) tc  ->
                   D.typeOfExpression' P S G (Conditional e1 e2 e3) tc' ->
                   tc = tc'.
Proof.
  intros Hunique1 Hunique2 Hunique3.
  inversion_clear 1; inversion_clear 1;
  repeat match goal with
  | [ Hunique : forall _ _, D.typeOfRValue P S G ?e _ -> D.typeOfRValue P S G ?e _ -> _ = _
    , H1 : D.typeOfRValue P S G ?e ?t1, H2 : D.typeOfRValue P S G ?e ?t2 |- _] => notSame t1 t2; pose proof (Hunique _ _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.usualArithmetic P ?t1 ?t2 ?t, H2 : D.usualArithmetic P ?t1 ?t2 ?t' |- _] => notSame t t'; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ H1 : D.composite ?t1 ?t2 ?t, H2 : D.composite ?t1 ?t2 ?t' |- _] => notSame t t'; pose proof (composite_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | [ Hunique : forall _ _, D.typeOfRValue P S G ?e _ -> D.typeOfRValue P S G ?e _ -> _ = _
    , Hnull : D.nullPointerConstant ?e
    , H : D.typeOfRValue P S G ?e (Pointer _ ?t) |- _] =>
      notSame t Void;
      let H' := fresh in
      destruct (@nullPointerConstant_typeOfRValue _ _ _ P S G e Hnull) as [[H' | H']| H'];
      [ discriminate (Hunique _ _ H H')
      | let Heq := fresh in set (Hunique _ _ H H') as Heq; inversion Heq; clear Heq; subst
      | destruct (H' _ H)]
  | _ => progress types_tac
  end.
Qed.

Lemma typeOfExpression'_neg_conditional1 {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A} :
  (forall t, neg (D.typeOfRValue P S G e1 t)) ->
  forall tc, neg (D.typeOfExpression' P S G (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Lemma typeOfExpression'_neg_conditional2 {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A} :
  (forall t, neg (D.typeOfRValue P S G e2 t)) ->
  forall tc, neg (D.typeOfExpression' P S G (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Lemma typeOfExpression'_neg_conditional3 {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A} : 
  (forall t, neg (D.typeOfRValue P S G e3 t)) ->
  forall tc, neg (D.typeOfExpression' P S G (Conditional e1 e2 e3) tc).
Proof. intros ?; inversion 1; firstorder. Qed.

Definition type_of_expression'_spec {A B1 B2} P (S : sigma B1 B2) G (e : expression' A) :=
  optionSpec   (type_of_expression' P S G e) (D.typeOfExpression' P S G e) *
  optionUnique (type_of_expression' P S G e) (D.typeOfExpression' P S G e).

Definition type_of_expression_spec {A B1 B2} P (S : sigma B1 B2) G (e : expression A) :=
  optionSpec   (type_of_expression P S G e) (D.typeOfExpression P S G e) *
  optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e).

Definition well_typed_arguments_spec {A B1 B2} P (S : sigma B1 B2) G (es : list (expression A)) :=
  forall ps, boolSpec (well_typed_arguments P S G es ps) (D.typeOfArguments P S G es ps).

Definition type_of_expression'_correct_Constant {A B1 B2} {P} {S : sigma B1 B2} {G} {c} :
  type_of_expression'_spec (A:=A) P S G (Constant c).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' (A:=A) P S G (Constant c)).
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

Lemma type_of_expression'_correct_Unary {A B1 B2} {P} {S : sigma B1 B2} {G} {aop} {e : expression A} :
  type_of_expression_spec P S G e ->
  type_of_expression'_spec P S G (Unary aop e).
Proof.
  intros [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Unary aop e)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold option_bind.
  unfold option_map.
  unfold andb.
  unfold orb.
  destruct aop;
  repeat match goal with
  | |- type_of_rvalue P S G e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
  | |- type_of_expression P S G e = _ -> _ => case_fun Hcorrect
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
  | H : D.typeOfLValue P S G _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P S G ?e ?t1 
  , H2 : D.typeOfRValue P S G ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux Hunique H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.promotion P ?t ?t1 
  , H2 : D.promotion P ?t ?t2 |- _ => notSame t1 t2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.typeOfExpression P S G ?e ?t1 
  , H2 : D.typeOfExpression P S G ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux Hunique H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.lvalueConversion ?t ?t1 
  , H2 : D.lvalueConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (lvalueConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | |- _ => finish fail
  | _ => progress types_tac
  end).
Qed.

Lemma type_of_expression'_correct_Binary_Comma {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Comma e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Comma e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold option_bind.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1 
  , H2 : D.typeOfRValue P S G ?e ?t2 |- ?t1 = ?t2 => eapply typeOfRValue_functional_aux; eassumption
  | H : forall _, neg _ |- False => eapply H; eassumption
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Mul {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Mul) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Mul) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1 
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Div {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Div) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Div) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1 
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic P ?t ?t' ?t1 
  , H2 : D.usualArithmetic P ?t ?t' ?t2 |- _ => notSame t1 t2; pose proof (usualArithmetic_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | _ : neg (D.arithmetic ?t1), H : D.wellTypedBinaryArithmetic ?t1 _ _ |- _ => inversion_clear H; contradiction
  | _ : neg (D.arithmetic ?t2), H : D.wellTypedBinaryArithmetic _ _ ?t2 |- _ => inversion_clear H; contradiction
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Lemma type_of_expression'_correct_Binary_Arithmetic_Mod {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Mod) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Mod) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
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

Definition type_of_expression'_correct_Binary_Arithmetic_Add {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Add) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Add) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
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

Definition type_of_expression'_correct_Binary_Arithmetic_Sub {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Sub) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Sub) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Arithmetic_Shl {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Shl) e2).
Proof. 
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Shl) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Arithmetic_Shr {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Shr) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Shr) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Band {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Band) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Band) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Bor {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Bor) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Bor) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Xor {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 (Arithmetic Xor) e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 (Arithmetic Xor) e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_And {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 And e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 And e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Or {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Or e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Or e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => progress types_tac
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Lt {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Lt e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Lt e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Gt {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Gt e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Gt e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Le {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Le e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Le e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Ge {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Ge e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Ge e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Binary_Eq {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Eq e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Eq e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | H1 : D.typeOfRValue P S G e1 _ , H2 : D.typeOfRValue P S G e2 _ |- well_typed_equality ?t1 ?t2 (null_pointer_constant ?e1) (null_pointer_constant ?e2)  = _ -> _ =>
      case_fun (well_typed_equality_correct
              (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique1)
              (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique2) H1 H2 (inl (eq_refl Eq)))
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H2 : neg (D.typeOfExpression' P S G (Binary e1 Eq e2) (RValueType (Basic (Integer (Signed Int))))) |- False => apply H2; econstructor (eassumption)
  | _ => finish fail
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Binary_Ne {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Binary e1 Ne e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Binary e1 Ne e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  unfold option_bind.
  unfold option_map.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | H1 : D.typeOfRValue P S G e1 _ , H2 : D.typeOfRValue P S G e2 _ |- well_typed_equality ?t1 ?t2 (null_pointer_constant ?e1) (null_pointer_constant ?e2)  = _ -> _ =>
      case_fun (well_typed_equality_correct
              (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique1)
              (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique2) H1 H2 (inr (eq_refl Ne)))
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H2 : neg (D.typeOfExpression' P S G (Binary e1 Ne e2) (RValueType (Basic (Integer (Signed Int))))) |- False => apply H2; econstructor (eassumption)
  | _ => finish fail
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_Assign {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (Assign e1 e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Assign e1 e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  fold (@assignable A B1 B2 P S G).
  unfold andb.
  repeat match goal with
  | |- type_of_expression P S G e1 = _ -> _ => case_fun Hcorrect1
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- assignable P S G (pointer_conversion ?t) e2 = _ -> _ => pose proof (pointer_conversion_correct t); case_fun (assignable_correct_aux (t1:=pointer_conversion t) Hcorrect2 Hunique2)
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
  | H : D.typeOfLValue P S G _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.typeOfExpression P S G ?e ?t1
  , H2 : D.typeOfExpression P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : findSpec ?t1 (D.pointerConversion ?t)
  , H2 : D.pointerConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (pointerConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ : forall _, neg (D.typeOfRValue P S G ?e _), H : D.assignable P S G _ ?e |- False => inversion_clear H
  | _ => reflexivity
  | H : _ + _ |- _ => destruct H as [? | ?]
  end.
Qed.

Definition type_of_expression'_correct_CompoundAssign {A B1 B2} {P} {S : sigma B1 B2} {G} {aop} {e1 e2 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression'_spec P S G (CompoundAssign e1 aop e2).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (CompoundAssign e1 aop e2)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold option_bind.
  unfold andb.
  unfold orb.
  repeat match goal with
  | |- type_of_expression P S G e1 = _ -> _ => case_fun Hcorrect1
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
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
  | H : D.typeOfLValue P S G _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : D.typeOfExpression P S G ?e ?t1
  , H2 : D.typeOfExpression P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfExpression_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
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

Definition type_of_expression'_correct_Conditional {A B1 B2} {P} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A} :
  type_of_expression_spec P S G e1 ->
  type_of_expression_spec P S G e2 ->
  type_of_expression_spec P S G e3 ->
  type_of_expression'_spec P S G (Conditional e1 e2 e3).
Proof.
  intros [Hcorrect1 Hunique1] [Hcorrect2 Hunique2] [Hcorrect3 Hunique3].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Conditional e1 e2 e3)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold option_bind.
  repeat match goal with
  | |- type_of_rvalue P S G e1 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect1 Hunique1)
  | |- type_of_rvalue P S G e2 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect2 Hunique2)
  | |- type_of_rvalue P S G e3 = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect3 Hunique3)
  | H1 : D.typeOfRValue P S G e1 _
  , H2 : D.typeOfRValue P S G e2 _
  , H3 : D.typeOfRValue P S G e3 _
    |- well_typed_conditional P _ _ _ (null_pointer_constant e2) (null_pointer_constant e3) = _ -> _ =>
      case_fun (well_typed_conditional_correct_aux
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique1)
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique2)
                  (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique3)
                  H1 H2 H3)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ * _ => split
  end;
  match goal with
  | |- optionSpec _ _ => assumption
  | H1 : D.typeOfExpression' P S G (Conditional _ _ _) _ |- optionUnique (Some _) _ =>
      let H2 := fresh in
      intros ? H2;
      apply f_equal;
      exact (typeOfExpression'_functional_conditional
               (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique1)
               (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique2)
               (@typeOfRValue_functional_aux _ _ _ _ _ _ _ Hunique3) H1 H2)
  | H1 : forall _, neg (D.typeOfExpression' P S G (Conditional _ _ _) _) |- optionUnique None _ =>
      let H2 := fresh in
      intros ? H2; destruct (H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P S G e1 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional1 H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P S G e2 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional2 H1 _ H2)
  | H1 : forall _ : ctype, neg (D.typeOfRValue P S G e3 _) |- _ =>
      let H2 := fresh in
      intros ? H2; destruct (typeOfExpression'_neg_conditional3 H1 _ H2)
  end.
Qed.

Definition type_of_expression'_correct_Cast {A B1 B2} {P} {S : sigma B1 B2} {G} {q} {t} {e : expression A} :
  type_of_expression_spec P S G e ->
  type_of_expression'_spec P S G (Cast q t e).
Proof.
  intros [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Cast q t e)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  unfold andb.
  repeat match goal with
  | |- type_of_rvalue P S G e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => reflexivity
  end.
Qed.

Definition type_of_expression'_correct_Call {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} {es} :
  well_typed_arguments_spec P S G es ->
  type_of_expression_spec P S G e ->
  type_of_expression'_spec P S G (Call e es).
Proof.
  intros Hargs [Hcorrect Hunique].
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' P S G (Call e es)); simpl.
  fold (@type_of_rvalue A B1 B2 P S G).
  fold (@assignable A B1 B2 P S G).
  fold (@well_typed_arguments A B1 B2 P S G).
  unfold andb.
  repeat match goal with
  | |- type_of_rvalue P S G e = _ -> _ => case_fun (type_of_rvalue_correct_aux Hcorrect Hunique)
  | |- well_typed_arguments P S G ?es ?ps = _ -> _ => case_fun (Hargs ps)
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
  | H1 : D.typeOfRValue P S G ?e ?t1
  , H2 : D.typeOfRValue P S G ?e ?t2
  , H  : optionUnique _ (D.typeOfExpression P S G ?e) |- _ => notSame t1 t2; pose proof (typeOfRValue_functional_aux H H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish fail
  end.
Qed.

Definition type_of_expression'_correct_Var {A B1 B2} {P} {S : sigma B1 B2} {G} {v} :
  D.disjoint G S ->
  type_of_expression'_spec (A:=A) P S G (Var v).
Proof.
  intros Hdisjoint.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' (A:=A) P S G (Var v)); simpl.
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

Definition type_of_expression'_correct_SizeOf {A B1 B2} {P} {S : sigma B1 B2} {G} {q} {t} :
  type_of_expression'_spec (A:=A) P S G (SizeOf q t).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' (A:=A) P S G (SizeOf q t)); simpl.
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

Definition type_of_expression'_correct_AlignOf {A B1 B2} {P} {S : sigma B1 B2} {G} {q} {t} :
  type_of_expression'_spec (A:=A) P S G (AlignOf q t).
Proof.
  unfold type_of_expression'_spec.
  pull_out (option typeCategory) (type_of_expression' (A:=A) P S G (AlignOf q t)); simpl.
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

Definition well_typed_arguments_correct_nil {A B1 B2} {P} {S : sigma B1 B2} {G} :
  well_typed_arguments_spec (A:=A) P S G nil.
Proof.
  destruct ps; simpl.
  - constructor.
  - inversion 1.
Qed.

Definition well_typed_arguments_correct_cons {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} {es} :
  type_of_expression_spec P S G e ->
  well_typed_arguments_spec P S G es ->
  well_typed_arguments_spec P S G (e :: es).
Proof.
  intros [Hcorrect Hunique] Hargs ps.
  pull_out bool (well_typed_arguments P S G (e :: es) ps); simpl.
  unfold andb.
  repeat match goal with
  | |- assignable P S G (pointer_conversion ?t) e = _ -> _ => pose proof (pointer_conversion_correct t); case_fun (assignable_correct_aux (t1:=pointer_conversion t) Hcorrect Hunique)
  | |- well_typed_arguments P S G ?es ?ps = _ -> _ => case_fun (Hargs ps)
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

Definition type_of_expression_correct_AnnotatedExpression {A B1 B2} {P} {S : sigma B1 B2} {G} {a} {e : expression' A} :
  type_of_expression'_spec P S G e ->
  type_of_expression_spec P S G (AnnotatedExpression a e).
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
  | H1 : D.typeOfExpression' P S G ?e ?t1
  , H  : optionUnique (Some ?t2) (D.typeOfExpression' P S G ?e) |- _ => notSame t1 t2; pose proof (H _ H1); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  end; reflexivity.
Qed.

Definition type_of_expression_correct_unique {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, type_of_expression_spec P S G e.
Proof.
  intros Hdisjoint.
  eapply (expression_nrect (fun e => type_of_expression'_spec P S G e)
                           (fun e => type_of_expression_spec  P S G e)
                           (fun es => well_typed_arguments_spec P S G es));
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

Definition type_of_expression_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, optionSpec (type_of_expression P S G e) (D.typeOfExpression P S G e).
Proof.
  intros Hdisjoint e.
  destruct (type_of_expression_correct_unique P Hdisjoint e) as [? _].
  assumption.
Qed.

Definition type_of_expression_unique {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, optionUnique (type_of_expression P S G e) (D.typeOfExpression P S G e).
Proof.
  intros Hdisjoint e.
  destruct (type_of_expression_correct_unique P Hdisjoint e) as [_ ?].
  assumption.
Qed.

Lemma typeOfExpression_functional {A B1 B2} {P} {S : sigma B1 B2} {G} {e : expression A} (Hdisjoint : D.disjoint G S) :
  forall {tc1 tc2},
    D.typeOfExpression P S G e tc1 ->
    D.typeOfExpression P S G e tc2 ->
    tc1 = tc2.
Proof.
  intros ? ? H1 H2.
  set (type_of_expression_unique P Hdisjoint e _ H1).
  set (type_of_expression_unique P Hdisjoint e _ H2).
  congruence.
Qed.
Arguments typeOfExpression_functional : default implicits.

Lemma typeable_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, boolSpec (typeable P S G e) (D.typeable P S G e).
Proof.
  intros Hdisjoint e.
  unfold typeable.
  pose proof (type_of_expression_correct P Hdisjoint e).
  optionSpec_destruct; simpl.
  - econstructor; eassumption.
  - inversion_clear 1; firstorder.
Qed.

Definition type_of_rvalue_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, optionSpec (type_of_rvalue P S G e) (D.typeOfRValue P S G e).
Proof.
  intros Hdisjoint e.
  apply type_of_rvalue_correct_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.

Definition type_of_rvalue_unique {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall e : expression A, optionUnique (type_of_rvalue P S G e) (D.typeOfRValue P S G e).
Proof.
  intros Hdisjoint e.
  apply type_of_rvalue_unique_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.

Lemma typeOfRValue_functional {A B1 B2} {P} {S : sigma B1 B2} {G} (Hdisjoint : D.disjoint G S) :
  forall (e : expression A) {t1 t2},
    D.typeOfRValue P S G e t1 ->
    D.typeOfRValue P S G e t2 ->
    t1 = t2.
Proof.
  intros e ? ? H1 H2.
  set (type_of_rvalue_unique P Hdisjoint e _ H1).
  set (type_of_rvalue_unique P Hdisjoint e _ H2).
  congruence.
Qed.

Lemma assignable_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall t1 (e2 : expression A), boolSpec (assignable P S G t1 e2) (D.assignable P S G t1 e2).
Proof.
  intros Hdisjoint t1 e2.
  apply assignable_correct_aux.
  apply type_of_expression_correct; assumption.
  apply type_of_expression_unique; assumption.
Qed.

Lemma well_formed_binding_correct b :
  boolSpec (well_formed_binding b) (D.wellFormedBinding b).
Proof.
  do 2 unfold_goal.
  repeat context_destruct.
  case_fun (wf_lvalue_correct q c); my_auto.
Qed.

Lemma well_formed_bindings_correct bs :
  boolSpec (well_formed_bindings bs) (D.wellFormedBindings bs).
Proof.
  do 2 unfold_goal.
  unfold andb.
  repeat match goal with
  | |- all_list _ _ = _ -> _ => case_fun (all_list_correct well_formed_binding_correct bs)
  | |- disjoint_bindings _ _ = _ -> _ => case_fun (disjoint_bindings_correct eq_identifier_correct bs)
  | _ => context_destruct
  end; my_auto.
Qed.

Lemma well_typed_block_correct_aux {A1 A2 B1 B2} P {S : sigma B1 B2} {G} {t_return} :
  (forall  s : statement A1 A2, boolSpec (well_typed_statement P S G t_return s) (D.wellTypedStatement P S G t_return s)) ->
  (forall ss : list (statement A1 A2), boolSpec (well_typed_block P S G t_return ss) (allList (D.wellTypedStatement P S G t_return) ss)).
Proof.
  intros well_typed_statement_correct.
  induction ss; simpl;
  unfold boolSpec;
  unfold andb;
  repeat match goal with
  | |- well_typed_statement P S G t_return ?s = _ -> _ => case_fun (well_typed_statement_correct s)
  | |- well_typed_block P S G t_return ?ss = _ -> _ => case_fun IHss
  | _ => context_destruct
  | |- allList _ _ => constructor; assumption
  | |- neg _ =>  inversion_clear 1; contradiction
  end.
Qed.

Lemma well_typed_definition_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall (d : identifier * expression A), boolSpec (well_typed_definition P S G d) (D.wellTypedDefinition P S G d).
Proof.
  intros Hdisjoint d.
  do 2 unfold_goal.
  repeat match goal with
  | |- lookup G ?v = _ -> _ => case_fun (lookup_correct G v)
  | |- assignable P S G ?t ?e = _ -> _ => case_fun (assignable_correct P Hdisjoint t e)
  | _ => context_destruct
  | |- D.wellTypedDefinition _ _ _ _ =>  econstructor; eassumption
  | |- neg _ => inversion_clear 1;
                repeat match goal with
                | H1 : D.lookup ?C ?v ?r1
                , H2 : D.lookup ?C ?v ?r2 |- _ => notSame r1 r2; pose proof (lookup_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
                | H : forall _, neg _ |- _ => eapply H; eassumption
                | _ => contradiction
                end
  end.
Qed.

Lemma well_typed_definitions_correct {A B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall (ds : list (identifier * expression A)), boolSpec (well_typed_definitions P S G ds) (allList (D.wellTypedDefinition P S G) ds).
Proof.
  intros Hdisjoint.
  apply all_list_correct.
  apply well_typed_definition_correct.
  assumption.
Qed.

Lemma well_typed_statement_correct {A1 A2 B1 B2} P {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall t_return (s : statement A1 A2),
    boolSpec (well_typed_statement P S G t_return s) (D.wellTypedStatement P S G t_return s).
Proof.
  intros Hdisjoint t_return s.
  revert s G Hdisjoint.
  eapply (
    statement_nrect
      (fun s  => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_statement' P S G t_return s ) (D.wellTypedStatement' P S G t_return s))
      (fun s  => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_statement  P S G t_return s ) (D.wellTypedStatement P S G t_return s))
      (fun ss => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_block      P S G t_return ss) (allList (D.wellTypedStatement P S G t_return) ss))
  );
  intros; simpl;
  match goal with
  | |- context [well_typed_block_aux (well_typed_statement _ _ ?G _) ?ss] => fold (@well_typed_block A1 A2 B1 B2 P S G t_return ss)
  | _ => idtac
  end;
  unfold boolSpec; unfold andb;
  repeat match goal with
  | |- fresh_bindings ?bs ?C = _ -> _ => case_fun (fresh_bindings_correct C bs)
  | |- typeable _ _ ?G ?e = _ -> _ => case_fun (typeable_correct P Hdisjoint e)
  | |- assignable _ _ ?G ?t1 ?e2 = _ -> _ => case_fun (assignable_correct P Hdisjoint t1 e2)
  | |- type_of_rvalue _ _ ?G ?e = _ -> _ => case_fun (type_of_rvalue_correct P Hdisjoint e)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- type_of_constant _ ?ic = _ -> _ => case_fun (type_of_constant_correct P ic)
  | |- well_typed_definitions _ _ ?G ?ds = _ -> _ => case_fun (well_typed_definitions_correct P Hdisjoint ds)
  | |- well_formed_bindings ?bs = _ -> _ => case_fun (well_formed_bindings_correct bs)
  | IH : forall _ _, boolSpec _ (D.wellTypedStatement  _ _ _ _ ?s) |- well_typed_statement  _ _ ?G _ ?s = _ -> _ => case_fun (IH G Hdisjoint)
  | IH : forall _ _, boolSpec _ (D.wellTypedStatement' _ _ _ _ ?s) |- well_typed_statement' _ _ ?G _ ?s = _ -> _ => case_fun (IH G Hdisjoint)
  | IH : forall _ _, boolSpec _ (allList (D.wellTypedStatement _ _ _ _) ?ss) |- well_typed_block _ _ ?G _ ?ss = _ -> _ =>
      is_var G; case_fun (IH _ Hdisjoint)
  | H : D.wellFormedBindings _, IH : forall _ _, boolSpec _ (allList (D.wellTypedStatement _ _ _ _) ?ss) |- well_typed_block _ _ ?G _ ?ss = _ -> _ =>
      not_var G;
      let IH' := fresh in
      assert (boolSpec (well_typed_block P S G t_return ss) (allList (D.wellTypedStatement P S G t_return) ss))
        as IH'
        by (apply IH; apply disjoint_freshBindings; [inversion_clear H|..]; assumption);
      case_fun IH'
  | _ => context_destruct
  | |- D.wellTypedStatement' _ _ _ _ _ => now my_auto
  | |- D.wellTypedStatement  _ _ _ _ _ => now my_auto
  | |- allList _ _ => now my_auto
  end;
  inversion 1; subst;
  repeat match goal with
  | H1 : D.typeOfRValue P S _ ?e ?t1
  , H2 : D.typeOfRValue P S _ ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfRValue_functional Hdisjoint _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H :  neg (?c = ?c) |- False => apply H; constructor
  end.
Qed.

Lemma well_typed_function_correct {A1 A2 B1 B2 : Set} P (S : sigma B1 B2) (p : _ * _ * statement A1 A2) :
  boolSpec (well_typed_function P S p) (D.wellTypedFunction P S p).
Proof.
  do 2 unfold_goal.
  unfold andb.
  repeat match goal with
  | |- fresh_bindings ?bs ?S = _ -> _ => case_fun (fresh_bindings_correct S bs)
  | |- well_formed_bindings ?bs = _ -> _ => case_fun (well_formed_bindings_correct bs)
  | |- AilWf.wf_type ?t = _ -> _ => case_fun (wf_type_correct t)
  | H : D.wellFormedBindings ?bs |- well_typed_statement _ _ (add_bindings ?bs empty) ?t ?s = _ -> _ =>
      notHyp (D.disjoint (add_bindings b empty) S);
      let Hdisjoint := fresh in
      assert (D.disjoint (add_bindings b empty) S) as Hdisjoint
        by (
          apply disjoint_freshBindings; [
              inversion_clear H; assumption
            | assumption
            | intros ? [? Hfalse]; inversion Hfalse
          ]
        );
      case_fun (well_typed_statement_correct P Hdisjoint t s)
  | _ => context_destruct
  | |- D.wellTypedFunction _ _ _ =>  constructor; assumption
  | |- neg _ => now (inversion 1; my_auto)
  end.
Qed.
 
Ltac typeOfExpression_equiv_tac S1 S2 :=
  match goal with
  | Hlookup     : D.lookup S1 _ _
  , HequivSigma : D.equivSigma S1 S2 |- D.typeOfExpression' _ S2 _ (Var _) (RValueType (type_from_sigma _)) => destruct ((fst HequivSigma) _ _ Hlookup) as [? [? [? ?]]]; econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivExpression ?e1 _ -> D.typeOfExpression _ S1 _ ?e1 _ -> D.typeOfExpression _ S2 _ _ _
  , _  : D.equivExpression ?e1 ?e2 |- D.typeOfExpression _ S2 _ ?e2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfExpression _ S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivExpression' ?e1 _ -> D.typeOfExpression' _ S1 _ ?e1 _ -> D.typeOfExpression' _ S2 _ _ _
  , _  : D.equivExpression' ?e1 ?e2 |- D.typeOfExpression' _ S2 _ ?e2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfExpression' _ S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivArguments ?es1 _ -> D.typeOfArguments _ S1 _ ?es1 _ -> D.typeOfArguments _ S2 _ _ _
  , _  : D.equivArguments ?es1 ?es2 |- D.typeOfArguments _ S2 _ ?es2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfArguments _ S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | H : D.typeOfRValue _ _ _ ?e1 _
  , _  : D.equivExpression ?e1 ?e2 |- D.typeOfRValue _ _ _ ?e2 _ => inversion_clear H; econstructor (now typeOfExpression_equiv_tac S1 S2)
  | H : D.typeOfLValue _ _ _ ?e1 _ _
  , _  : D.equivExpression ?e1 ?e2 |- D.typeOfLValue _ _ _ ?e2 _ _ => inversion_clear H; econstructor (now typeOfExpression_equiv_tac S1 S2)
  | H : D.assignable _ _ _ _ ?e1
  , _  : D.equivExpression ?e1 ?e2 |- D.assignable _ _ _ _ ?e2 => inversion H; subst; econstructor (now typeOfExpression_equiv_tac S1 S2)
  | |- D.nullPointerConstant _ => eapply nullPointerConstant_equiv; eassumption
  | _ : D.equivExpression ?e1 ?e2
  , H : neg (D.nullPointerConstant ?e1) |- neg (D.nullPointerConstant ?e2) => intros ?; apply H; eapply nullPointerConstant_equiv; [eapply equivExpression_symm; eassumption | assumption]
  | _ => solve [eassumption|reflexivity]
  | |- type_from_sigma _ = type_from_sigma _ => unfold type_from_sigma; congruence
  end.

Lemma typeOfExpression_equiv {A1 A2 B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2} {t},
    D.equivExpression e1 e2 ->
    D.typeOfExpression P S1 G e1 t ->
    D.typeOfExpression P S2 G e2 t.
Proof.
  intros HequivSigma.
  apply (
    expression_nrect
      (fun x => forall (y : expression' A2) t (Hequiv : D.equivExpression' x y) (Ht1 : D.typeOfExpression' P S1 G x t), D.typeOfExpression' P S2 G y t)
      (fun x => forall y t (Hequiv : D.equivExpression x y) (Ht1 : D.typeOfExpression P S1 G x t), D.typeOfExpression P S2 G y t)
      (fun x => forall (y : list (expression A2)) p (Hequiv : D.equivArguments x y) (Ht1 : D.typeOfArguments P S1 G x p), D.typeOfArguments P S2 G y p)
  ); intros; inversion Hequiv; subst; inversion Ht1; subst;
  now typeOfExpression_equiv_tac S1 S2.
Qed.

Lemma typeable_equiv {A1 A2 B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2},
    D.equivExpression e1 e2 ->
    D.typeable P S1 G e1 ->
    D.typeable P S2 G e2.
Proof. inversion_clear 3. econstructor; eapply typeOfExpression_equiv; eassumption. Qed.

Lemma typeOfRValue_equiv {A1 A2 B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2} {t},
    D.equivExpression e1 e2 ->
    D.typeOfRValue P S1 G e1 t ->
    D.typeOfRValue P S2 G e2 t.
Proof.
  inversion_clear 3;
  repeat match goal with
  | H : D.typeOfLValue _ _ _ _ _ _ |- _ => inversion_clear H
  end;
  econstructor (
    solve [
        eassumption
      | eapply typeOfExpression_equiv; eassumption
      | econstructor; eapply typeOfExpression_equiv; eassumption
    ]
  ).
Qed.

Lemma assignable_equiv {A A' B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {t1} {e2 : expression A} {e2' : expression A'},
    D.equivExpression e2 e2' ->
    D.assignable P S1 G t1 e2 ->
    D.assignable P S2 G t1 e2'.
Proof.
  inversion_clear 3;
  econstructor (
    solve [
        eassumption
      | eapply typeOfRValue_equiv; eassumption
      | eapply typeOfExpression_equiv; eassumption
      | eapply nullPointerConstant_equiv; eassumption
      ]
    ).
Qed.

Lemma wellTypedDeclaration_equiv {A1 A2 B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {ds1 : list (_ * expression A1)} {ds2 : list (_ * expression A2)},
    D.equivDeclaration ds1 ds2 ->
    allList (D.wellTypedDefinition P S1 G) ds1 ->
    allList (D.wellTypedDefinition P S2 G) ds2.
Proof.
  induction ds1; inversion_clear 1; intros Ht1.
  - constructor.
  - inversion_clear Ht1.
    constructor.
    + match goal with
      | H : D.wellTypedDefinition _ S1 _ _ |- _ => inversion_clear H
      end.
      econstructor.
      * eassumption.
      * eapply assignable_equiv; eassumption.
    + eapply IHds1; eassumption.
Qed.

Lemma freshBindings_equivSigma {A1 A2 B1 B2 : Set} {S1 : sigma A1 B1} {S2 : sigma A2 B2} :
  D.equivSigma S1 S2 ->
  forall {bs : bindings},
    D.freshBindings bs S1 ->
    D.freshBindings bs S2.
Proof.
  intro Hequiv.
  eapply freshBindings_equiv.
  eapply equiv_weaken; now eauto.
Qed.
  
Lemma wellTypedStatement_equiv {A1 A1' A2 A2' B1 B1' B2 B2'} {P} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} :
  D.equivSigma S1 S2 ->
  forall {s1 : statement A1 A1'} {s2 : statement A2 A2'} {t_return},
    D.equivStatement s1 s2 ->
    D.wellTypedStatement P S1 G t_return s1 ->
    D.wellTypedStatement P S2 G t_return s2.
Proof.
  intros HequivSigma s1 s2 t_return.
  revert s1 s2 G.
  eapply (
    statement_nrect
      (fun x => forall (y : statement' A2 A2') G (Hequiv : D.equivStatement' x y) (Ht1 : D.wellTypedStatement' P S1 G t_return x), D.wellTypedStatement' P S2 G t_return y)
      (fun x => forall (y : statement A2 A2') G (Hequiv : D.equivStatement x y) (Ht1 : D.wellTypedStatement P S1 G t_return x), D.wellTypedStatement P S2 G t_return y)
      (fun x => forall (y : list (statement A2 A2')) G (Hequiv : D.equivBlock x y) (Ht1 : allList (D.wellTypedStatement P S1 G t_return) x), allList (D.wellTypedStatement P S2 G t_return) y)
  ); intros; inversion Hequiv; subst; inversion Ht1; subst;
  econstructor;
  match goal with
  | H : forall _ _, _ -> D.wellTypedStatement _ _ _ _ ?s1 -> _
  , _ : D.equivStatement ?s1 ?s2 |-  D.wellTypedStatement _ S2 _ _ ?s2 => eapply H; eassumption
  | H : forall _ _, _ -> D.wellTypedStatement' _ _ _ _ ?s1 -> _
  , _ : D.equivStatement' ?s1 ?s2 |-  D.wellTypedStatement' _ S2 _ _ ?s2 => eapply H; eassumption
  | H : forall _ _, _ -> allList (D.wellTypedStatement _ _ _ _) ?ss1 -> _
  , _ : D.equivBlock ?ss1 ?ss2 |-  allList (D.wellTypedStatement _ S2 _ _) ?ss2 => eapply H; eassumption
  | |- D.typeable     _ S2 _ _   => eapply typeable_equiv; eassumption
  | |- D.assignable   _ S2 _ _ _ => eapply assignable_equiv; eassumption
  | |- D.typeOfRValue _ S2 _ _ _ => eapply typeOfRValue_equiv; eassumption
  | |- D.freshBindings _ S2 => eapply freshBindings_equivSigma; eassumption
  | |- allList (D.wellTypedDefinition _ S2 _) _ => eapply wellTypedDeclaration_equiv; eassumption
  | _ => eassumption
  end.
Qed.

Lemma wellTypedFunction_equiv {A1 A1' A2 A2' B1 B1' B2 B2': Set} {P} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} :
  D.equivSigma S1 S2 ->
  forall {p1 : _ * statement A1 A1'} {p2 : _ * statement A2 A2'},
    cross2 eq (@D.equivStatement A1 A2 A1' A2') p1 p2 ->
    D.wellTypedFunction P S1 p1 ->
    D.wellTypedFunction P S2 p2.
Proof.
  intros HequivSigma [[? ?] ?] [[? ?] ?] [Heq ?].
  inversion_clear Heq.
  inversion_clear 1.
  econstructor.
  - assumption.
  - eapply freshBindings_equivSigma; eassumption.
  - assumption.
  - eapply wellTypedStatement_equiv; eassumption.
Qed.

Lemma wellTypedSigma_equiv {A1 A1' A2 A2': Set} {P} {S1 : sigma A1 A1'} {S2 : sigma A2 A2'} :
  D.equivSigma S1 S2 ->
  D.wellTypedSigma P S1 ->
  D.wellTypedSigma P S2.
Proof.
  intros [Hsub1 Hsub2] Ht1.
  intros ? ? Hlookup2.
  destruct (Hsub2 _ _  Hlookup2) as [? [Hlookup1 ?]].
  set (Ht1 _ _ Hlookup1).
  eapply wellTypedFunction_equiv.
  constructor; eassumption.
  eassumption.
  eassumption.
Qed.

Lemma wellTypedProgram_equiv {A1 A1' A2 A2': Set} {P} :
  forall {p1 : program A1 A1'} {p2 : program A1 A1'},
    D.equivProgram p1 p2 ->
    D.wellTypedProgram P p1 ->
    D.wellTypedProgram P p2.
Proof.
  intros [? ?] [? ?] [Heq HequivSigma]; simpl in *; subst.
  inversion_clear 1.
  match goal with
  | H : D.lookup _ _ _ |- _ => destruct ((fst HequivSigma) _ _ H) as [[? ?] [? [? ?]]]; simpl in *; subst
  end.
  econstructor.
  - eassumption.
  - eapply wellTypedSigma_equiv; eassumption.
Qed.
