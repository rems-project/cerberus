Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.
Require Import Context.

Require Import GenTypes.
Require Import Annotation.
Require Import GenSyntaxAux.

Require Import AilTypes_proof.
Require Import AilSyntax_proof.
Require Import Context_proof.

Require Tactics.

Module D.
  Require Context_defns.
  Require AilSyntax_defns.
  Require GenSyntaxAux_defns.

  Include Context_defns.
  Include AilSyntax_defns.
  Include GenSyntaxAux_defns.
End D.


Lemma equiv_annotation_expression_correct {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (e1 : expression A1) (e2 : expression A2) :
  match equiv_annotation_expression A A' e1 e2 with
  | Some e2' => D.equivExpression e1 e2 /\ D.equivAnnotationExpression A A' e2 e2'
  | None     => ~ D.equivExpression e1 e2
  end.
Proof.
  revert e2.
  apply (
    expression_nrect
      (fun x => forall y, match equiv_annotation_expression' A A' x y with
                          | Some z => D.equivExpression' x y /\ D.equivAnnotationExpression' A A' y z
                          | None   => ~ D.equivExpression' x y
                          end)
      (fun x => forall y, match equiv_annotation_expression A A' x y with
                          | Some z => D.equivExpression x y /\ D.equivAnnotationExpression A A' y z
                          | None   => ~ D.equivExpression x y
                          end)
      (fun x => forall y, match equiv_annotation_arguments A A' x y with
                          | Some z => D.equivArguments x y /\ D.equivAnnotationArguments A A' y z
                          | None   => ~ D.equivArguments x y
                          end)
  ); intros; destruct y; simpl;
  repeat match goal with
  | |- context[equiv_annotation_arguments_aux A A' (equiv_annotation_expression A A') ?x ?y] =>
         fold (equiv_annotation_arguments A A' x y)
  end;
  unfold optionSpec;
  unfold option_bind;
  unfold andb;
  repeat match goal with
  | |- eq_unaryOperator ?x ?y = _ -> _ => case_fun (eq_unaryOperator_correct x y)
  | |- eq_binaryOperator ?x ?y = _ -> _ => case_fun (eq_binaryOperator_correct x y)
  | |- eq_arithmeticOperator ?x ?y = _ -> _ => case_fun (eq_arithmeticOperator_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_constant ?x ?y = _ -> _ => case_fun (eq_constant_correct x y)
  | IH : forall _, match equiv_annotation_expression A A' ?x _ with _ => _ end |- equiv_annotation_expression A A' ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, match equiv_annotation_expression' A A' ?x _ with _ => _ end |- equiv_annotation_expression' A A' ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, match equiv_annotation_arguments A A' ?x _ with _ => _ end |- equiv_annotation_arguments A A' ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; my_auto' fail ltac:(rewrite id_add_get; reflexivity).
Qed.

Lemma equivAnnotationExpression_equivExpression {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (e1 : expression A2) (e2 : expression A2') :
  D.equivAnnotationExpression A A' e1 e2 -> D.equivExpression e1 e2.
Proof.
  revert e2.
  apply (
    expression_nrect
      (fun x => forall y (HequivAnnot : D.equivAnnotationExpression' A A' x y), D.equivExpression' x y)
      (fun x => forall y (HequivAnnot : D.equivAnnotationExpression  A A' x y), D.equivExpression  x y)
      (fun x => forall y (HequivAnnot : D.equivAnnotationArguments   A A' x y), D.equivArguments   x y)

  ); intros; inversion HequivAnnot; subst; constructor; now firstorder.
Qed.

Lemma equiv_annotation_definition_correct {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (d1 : _ * expression A1) (d2 : _ * expression A2) :
  match equiv_annotation_definition A A' d1 d2 with 
  | Some d2' => D.equivDefinition d1 d2 /\ D.equivAnnotationDefinition A A' d2 d2'
  | None     => ~ D.equivDefinition d1 d2
  end.
Proof.
  do 2 unfold_goal.
  unfold option_bind.
  repeat match goal with
  | |- equiv_annotation_expression A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_expression_correct A A' x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Lemma equivAnnotationDefinition_equivDefinition {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (d1 : _ * expression A2) (d2 : _ * expression A2') :
  D.equivAnnotationDefinition A A' d1 d2 -> D.equivDefinition d1 d2.
Proof.
  inversion_clear 1.
  constructor.
  eapply equivAnnotationExpression_equivExpression; eassumption.
Qed.


Lemma equiv_annotation_declaration_correct {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (ds1 : list (_ * expression A1)) (ds2 : list(_ * expression A2)) :
  match equiv_annotation_declaration A A' ds1 ds2 with
  | Some ds2' => D.equivDeclaration ds1 ds2 /\ D.equivAnnotationDeclaration A A' ds2 ds2'
  | None      => ~ D.equivDeclaration ds1 ds2
  end.
Proof.
  revert ds2.
  induction ds1; intros; simpl;
  unfold optionSpec;
  unfold option_bind;
  repeat match goal with
  | |- equiv_annotation_definition A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_definition_correct A A' x y)
  | |- equiv_annotation_declaration A A' ?x ?y = _ -> _ => case_fun (IHds1 y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Lemma equivAnnotationDeclaration_equivDeclaration {A1 A2 A2' : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (ds1 : list (_ * expression A2)) (ds2 : list (_ * expression A2')) :
  D.equivAnnotationDeclaration A A' ds1 ds2 -> D.equivDeclaration ds1 ds2.
Proof.
  revert ds2.
  induction ds1; inversion_clear 1; constructor.
  - eapply equivAnnotationDefinition_equivDefinition; eassumption.
  - eapply IHds1; eassumption.
Qed.

Lemma equiv_annotation_statement_correct {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (s1 : statement B A1) (s2 : statement B A2) :
  match equiv_annotation_statement A A' s1 s2 with
  | Some s2' => D.equivStatement s1 s2 /\ D.equivAnnotationStatement A A' s2 s2'
  | None     => ~ D.equivStatement s1 s2
  end.
Proof.
  revert s2.
  apply (
    statement_nrect
      (fun x => forall y, match equiv_annotation_statement' A A' x y with
                          | Some z => D.equivStatement' x y /\ D.equivAnnotationStatement' A A' y z
                          | None   => ~ D.equivStatement' x y
                          end)
      (fun x => forall y, match equiv_annotation_statement  A A' x y with 
                          | Some z => D.equivStatement x y /\ D.equivAnnotationStatement A A' y z
                          | None   => ~ D.equivStatement x y
                          end)
      (fun x => forall y, match equiv_annotation_block A A' x y with
                          | Some z => D.equivBlock x y /\ D.equivAnnotationBlock A A' y z
                          | None   => ~ D.equivBlock x y
                          end)
  ); intros; destruct y; simpl;
  repeat match goal with
  | |- context[equiv_annotation_block_aux A A' (equiv_annotation_statement A A') ?ss1 ?ss2] => fold (equiv_annotation_block A A' ss1 ss2)
  end;
  unfold optionSpec;
  unfold option_bind;
  repeat match goal with
  | |- equiv_annotation_expression A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_expression_correct A A' x y)
  | IH : forall _, match equiv_annotation_block A A' ?x _ with _ => _ end |- equiv_annotation_block A A' ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, match equiv_annotation_statement A A' ?x _ with _ => _ end |- equiv_annotation_statement A A' ?x ?y = _ -> _ => case_fun (IH y)
  | IH : forall _, match equiv_annotation_statement' A A' ?x _ with _ => _ end|- equiv_annotation_statement' A A' ?x ?y = _ -> _ => case_fun (IH y)
  | |- equiv_annotation_declaration A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_declaration_correct A A' x y)
  | |- eq_integerConstant ?x ?y = _ -> _ => case_fun (eq_integerConstant_correct x y)
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | |- eq_bindings ?x ?y = _ -> _ => case_fun (eq_bindings_correct x y)
  | _ => context_destruct
  end; my_auto.
Qed.

Lemma equivAnnotationStatement_equivStatement {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (s1 : statement B A2) (s2 : statement B A2') :
  D.equivAnnotationStatement A A' s1 s2 -> D.equivStatement s1 s2.
Proof.
  revert s2.
  apply (
    statement_nrect
      (fun x => forall (y : statement' B A2')       (HannotEquiv : D.equivAnnotationStatement' A A' x y), D.equivStatement' x y)
      (fun x => forall y                            (HannotEquiv : D.equivAnnotationStatement  A A' x y), D.equivStatement  x y)
      (fun x => forall (y : list (statement B A2')) (HannotEquiv : D.equivAnnotationBlock      A A' x y), D.equivBlock      x y)
  );
  intros;
  inversion HannotEquiv; subst;
  constructor;
  solve [
    firstorder
  | eapply equivAnnotationExpression_equivExpression; eassumption
  | eapply equivAnnotationDeclaration_equivDeclaration; eassumption
  ].
Qed.

Lemma equiv_annotation_function_correct {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (p1 : _ * _ * statement B A1) (p2 : _ * _ * statement B A2) :
  match equiv_annotation_function A A' p1 p2 with
  | Some p2' => D.equivFunction p1 p2 /\ D.equivAnnotationFunction A A' p2 p2'
  | None     => ~ D.equivFunction p1 p2
  end.
Proof.
  do 2 unfold_goal.
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | |- equiv_annotation_statement A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_statement_correct A A' x y)
  | |- eq_bindings ?x ?y = _ -> _ => case_fun (eq_bindings_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | _ => context_destruct
  end; my_auto;
  inversion 1;
  Tactics.subst_no_fail; Tactics.autoinjections;
  match goal with
  | H : ?c <> ?c |- _ => congruence
  | H : forall _, ~ _ |- False => eapply H; split; eassumption
  end.
Qed.

Lemma equivAnnotationFunction_equivFunction {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (p1 : _ * _ * statement B A2) (p2 : _ * _ * statement B A2') :
  D.equivAnnotationFunction A A' p1 p2 -> D.equivFunction p1 p2.
Proof.
  inversion_clear 1.
  constructor.
  - assumption.
  - eapply equivAnnotationStatement_equivStatement; eassumption.
Qed.

Lemma equiv_annotation_sigma_correct_aux {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (S1 : sigma B A1) v (p2 : _ * _ * statement B A2) :
  match equiv_annotation_sigma_map A A' S1 v p2 with
  | Some p2' => (exists p1, D.lookup S1 v p1 /\ D.equivFunction p1 p2) /\ D.equivAnnotationFunction A A' p2 p2'
  | None     => ~ (exists p1, D.lookup S1 v p1 /\ D.equivFunction p1 p2) \/
                (exists p1, D.lookup S1 v p1 /\ D.equivFunction p1 p2) /\ forall p2' : _ * _ * statement B A2', ~ D.equivAnnotationFunction A A' p2 p2'
  end.
Proof.
  unfold_goal.
  unfold option_bind.
  repeat match goal with
  | |- equiv_annotation_function A A' ?x ?y = _ -> _ => case_fun (equiv_annotation_function_correct A A' x y)
  | |- AilSyntax.lookup S1 v = _ -> _ => case_fun (AilSyntax_proof.lookup_correct S1 v)
  | _ => context_destruct
  end;
  match goal with
  | |- _ /\ _ => intuition; eexists; split; eassumption
  | |- _ \/ _ =>
      left; intros [p1 [? ?]];
      repeat match goal with
      | H1 : D.lookup S1 v ?p1, H2 : D.lookup S1 v ?p2 |- _ =>
          notSame p1 p2;
          pose proof (lookup_functional H1 H2);
          Tactics.subst_no_fail; Tactics.autoinjections
       end;
      contradiction || now firstorder
  end.
Qed.

Lemma equiv_annotation_sigma_correct {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (S1 : sigma B A1) (S2 : sigma B A2) :
  match equiv_annotation_sigma A A' S1 S2 with
  | Some S2' => D.equivSigma S1 S2 /\ D.equivAnnotationSigma A A' S2 S2'
  | None     => ~ D.equivSigma S1 S2
  end.
Proof.
  unfold_goal.
  repeat match goal with
  | |- equiv_sigma S1 S2 = _ -> _ => case_fun (equiv_sigma_correct S1 S2)
  | |- mapP _ _ _ = _ -> _ => case_fun (mapP_correct _ eq_identifier_correct (equiv_annotation_sigma_correct_aux A A' S1) S2)
  | _ => context_destruct
  end; intuition.
  match goal with
  | H : exists _, _ |- False => destruct H as [v [p2 [Hlookup2 [Hfalse|[[p1 []] ?]]]]]; [
                                  apply Hfalse; exact ((proj2 H1) v p2 Hlookup2)
                                | pose proof (equiv_annotation_function_correct A A' p1 p2);
                                  destruct (equiv_annotation_function A A' p1 p2);
                                  now firstorder
                                ]
  end.
Qed.

Lemma equivAnnotationSigma_equivSigma {A1 A2 A2' B : Set} (A : annotation A1 A2) (A' : annotation A1 A2') (S1 : sigma B A2) (S2 : sigma B A2') :
  D.equivAnnotationSigma A A' S1 S2 -> D.equivSigma S1 S2.
Proof.
  intros HequivAnnot.
  split; [apply proj1 in HequivAnnot | apply proj2 in HequivAnnot]; intros v p Hlookup;
  destruct (HequivAnnot v p Hlookup) as [p' [Hlookup' HequivAnnotFunction]];
  exists p'; (split; [exact Hlookup' | eapply equivAnnotationFunction_equivFunction; eexact HequivAnnotFunction]).
Qed.
