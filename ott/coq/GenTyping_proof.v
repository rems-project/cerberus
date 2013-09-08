Require Import Common.

Require Import AilTypes.
Require Import AilSyntax.
Require Import AilSyntaxAux.
Require Import Implementation.
Require Import GenTypes.
Require Import GenTypesAux.
Require Import GenTyping.
Require Import GenSyntax.
Require Import Annotation.

Require Tactics.
Require Context_defns.

Require AilTypesAux.
Require AilTypesAux_defns.
Require AilTypesAux_proof.

Require AilTyping.
Require AilTyping_defns.
Require AilTyping_proof.

Module D.
Require AilSyntaxAux_defns.
Require GenTypesAux_defns.
Require GenTyping_defns.
Require Context_defns.
Require GenSyntax_defns.

Include AilSyntax_defns.
Include AilSyntaxAux_defns.
Include GenTypesAux_defns.
Include GenTyping_defns.
Include Context_defns.
Include GenSyntax_defns.
End D.

Require Import Context_proof.
Require Import Range_proof.
Require Import AilSyntax_proof.
Require Import AilSyntaxAux_proof.
Require Import GenTypesAux_proof.
Require Import GenSyntax_proof.

Local Open Scope type.

(* Section 1: typing of constants *)

Lemma type_of_constant_correct ic :
  findSpec (type_of_constant ic) (D.typeOfConstant ic).
Proof.
  repeat match goal with
  | H : (_ * _)%type |- _ => destruct H
  | H : option _ |- _ => destruct H
  | H : integerSuffix |- _ => destruct H
  end;
  my_auto;
  match goal with
  | |- context[AilTypesAux.in_min_integer_range ?n ?it] =>
      pose proof (AilTypesAux_proof.in_min_integer_range_correct n it); boolSpec_destruct; now my_auto
  end.
Qed.

Lemma typeOfConstant_functional {ic} {git1 git2} :
  D.typeOfConstant ic git1 ->
  D.typeOfConstant ic git2 ->
  git1 = git2.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  my_auto.
Qed.

Lemma typeOfConstant_interpret {ic} {git} :
  D.typeOfConstant ic git ->
  forall {P} {it},
    D.interpretGenIntegerType P git it ->
    AilTyping_defns.typeableConstant P ic ->
    AilTyping_defns.typeOfConstant P ic it.
Proof.
  inversion_clear 1;
  inversion_clear 1;
  inversion_clear 1;
  repeat match goal with
  | H : AilTyping_defns.signedOptionIntegerSuffix _ |- _ => inversion_clear H
  | H : AilTyping_defns.unsignedOptionIntegerSuffix _ |- _ => inversion_clear H
  | H : AilTyping_defns.signedIntegerSuffix _ |- _ => inversion_clear H
  | H : AilTyping_defns.unsignedIntegerSuffix _ |- _ => inversion_clear H
  end;
  now my_auto.
Qed.

Lemma typeOfConstant_inject {P} {ic} {it} :
  AilTyping_defns.typeOfConstant P ic it ->
  exists git,
    D.interpretGenIntegerType P git it /\
    D.typeOfConstant ic git.
Proof.
  intros HtypeOfConstant.
  pose proof (
    AilTypesAux_proof.integer_range_precision_signed
      (AilTypesAux_defns.Signed_Int P Int)
      (AilTypesAux_defns.Signed_Int P Long)
      (le_precision_Signed_Int_Long P)
  ).
  pose proof (
    AilTypesAux_proof.integer_range_precision_unsigned
      (AilTypesAux_defns.Unsigned_Int P Int)
      (AilTypesAux_defns.Unsigned_Int P Long)
      (le_precision_Unsigned_Int_Long P)
  ).
  exists (type_of_constant ic); split.
  - inversion_clear HtypeOfConstant; simpl;
    match goal with
    | Hfalse : ~ _ |- context[AilTypesAux.in_min_integer_range ?n ?it] =>
        pose proof (AilTypesAux_proof.in_min_integer_range_correct n it) as HinMin;
        boolSpec_destruct; [|do 2 constructor; assumption];
        pose proof (HinMin P) as HinP;
        apply AilTypesAux_proof.inIntegerRange_inversion in HinP;
        apply memNat_inversion in HinP;
        destruct HinP;
        exfalso; eapply Hfalse; constructor
    | _ => idtac
    end;
    solve [
      my_auto
    | eapply sub_mem; finish eassumption
    ].
  - exact (type_of_constant_correct ic).
Qed.

(* Section 2: well-annotated implies well-typed *)

Lemma wellAnnotatedLValue_typeOfLValue_aux {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} :
  (forall {gtc},
     D.wellAnnotatedExpression A S G e gtc ->
     D.typeOfExpression S G e gtc) ->
  forall {q} {t},
    D.wellAnnotatedLValue A S G e q t ->
    D.typeOfLValue S G e q t.
Proof. inversion_clear 2; constructor; firstorder. Qed.

Lemma wellAnnotatedRValue_typeOfRValue_aux {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} :
  (forall {gtc},
     D.wellAnnotatedExpression A S G e gtc ->
     D.typeOfExpression S G e gtc) ->
  forall {gt},
    D.wellAnnotatedRValue A S G e gt ->
    D.typeOfRValue S G e gt.
Proof.
  intros wellAnnotatedExpression_typeOfExpression.
  inversion_clear 1; try
  econstructor (
    solve [
      eapply wellAnnotatedExpression_typeOfExpression; eassumption
    | eapply (wellAnnotatedLValue_typeOfLValue_aux wellAnnotatedExpression_typeOfExpression); eassumption
    | assumption
    ]
  ).
Qed.

Lemma wellAnnotatedAssignee_assignable_aux {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e2 : expression A2} :
  (forall {gtc},
     D.wellAnnotatedExpression A S G e2 gtc ->
     D.typeOfExpression S G e2 gtc) ->
  forall {t1},
    D.wellAnnotatedAssignee A S G t1 e2 ->
    D.assignable S G t1 e2.
Proof. inversion_clear 2; econstructor (solve [eapply wellAnnotatedRValue_typeOfRValue_aux; eassumption|assumption]). Qed.

Lemma wellAnnotatedExpression_typeOfExpression {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} {gtc} :
  D.wellAnnotatedExpression A S G e gtc ->
  D.typeOfExpression S G e gtc.
Proof.
  revert gtc.
  apply (
    expression_nrect
      (fun x => forall gtc (Hannot : D.wellAnnotatedExpression' A S G x gtc), D.typeOfExpression' S G x gtc)
      (fun x => forall gtc (Hannot : D.wellAnnotatedExpression  A S G x gtc), D.typeOfExpression  S G x gtc)
      (fun x => forall p   (Hannot : D.wellAnnotatedArguments   A S G x p)  , D.typeOfArguments   S G x p)
  ); intros; inversion Hannot; subst;
  econstructor (
    now repeat match goal with
    | IH : forall _, _ -> ?c _ _ ?e _ |- ?c _ _ ?e _ => eapply IH; eassumption
    | |- D.typeOfRValue _ _ _ _   => eapply wellAnnotatedRValue_typeOfRValue_aux; eassumption
    | |- D.typeOfLValue _ _ _ _ _ => eapply wellAnnotatedLValue_typeOfLValue_aux; eassumption
    | |- D.assignable   _ _ _ _   => eapply wellAnnotatedAssignee_assignable_aux; eassumption
    | _ => eassumption
    end
  ).
Qed.

Lemma wellAnnotatedLValue_typeOfLValue {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} {q} {t} :
  D.wellAnnotatedLValue A S G e q t ->
  D.typeOfLValue S G e q t.
Proof.
  eapply (wellAnnotatedLValue_typeOfLValue_aux).
  eapply @wellAnnotatedExpression_typeOfExpression.
Qed.

Lemma wellAnnotatedRValue_typeOfRValue {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} {gt} :
  D.wellAnnotatedRValue A S G e gt ->
  D.typeOfRValue S G e gt.
Proof.
  eapply (wellAnnotatedRValue_typeOfRValue_aux).
  eapply @wellAnnotatedExpression_typeOfExpression.
Qed.

Lemma wellAnnotatedAssignee_assignable {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {t1} {e2 : expression A2} :
  D.wellAnnotatedAssignee A S G t1 e2 ->
  D.assignable S G t1 e2.
Proof.
  eapply (wellAnnotatedAssignee_assignable_aux).
  eapply @wellAnnotatedExpression_typeOfExpression.
Qed.

Lemma wellAnnotatedArguments_typeOfArguments {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {es : list (expression A2)} {p} :
  D.wellAnnotatedArguments A S G es p ->
  D.typeOfArguments S G es p.
Proof.
  revert p.
  induction es;
  inversion_clear 1;
  econstructor (
    now repeat first [
      eassumption
    | eapply wellAnnotatedAssignee_assignable
    | now firstorder
    ]
  ).
Qed.

Lemma wellAnnotatedExpression'_typeOfExpression' {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression' A2} {gtc} :
  D.wellAnnotatedExpression' A S G e gtc ->
  D.typeOfExpression' S G e gtc.
Proof.
  inversion_clear 1;
  econstructor (
    now repeat first [
      eassumption
    | eapply wellAnnotatedRValue_typeOfRValue
    | eapply wellAnnotatedLValue_typeOfLValue
    | eapply wellAnnotatedAssignee_assignable
    | eapply wellAnnotatedArguments_typeOfArguments
    | eapply wellAnnotatedExpression_typeOfExpression
    ]
  ).
Qed.

Lemma wellAnnotated_typeable {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {e : expression A2} :
  D.wellAnnotated A S G e ->
  D.typeable S G e.
Proof.
  inversion_clear 1.
  econstructor.
  eapply wellAnnotatedExpression_typeOfExpression; eassumption.
Qed.

Lemma wellAnnotatedDefinition_wellTypedDefinition {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {d : _ * expression A2} :
  D.wellAnnotatedDefinition A S G d ->
  D.wellTypedDefinition S G d.
Proof.
  inversion_clear 1.
  econstructor.
  - eassumption.
  - eapply wellAnnotatedAssignee_assignable; eassumption.
Qed.

Lemma wellAnnotatedDeclaration_wellTypedDeclaration {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {ds : list (_ * expression A2)} :
  allList (D.wellAnnotatedDefinition A S G) ds ->
  allList (D.wellTypedDefinition S G) ds.
Proof.
  induction ds;
  inversion_clear 1;
  econstructor.
  - eapply wellAnnotatedDefinition_wellTypedDefinition; eassumption.
  - eapply IHds; eassumption.
Qed.

Lemma wellAnnotatedStatement_wellTypedStatement {A1 A2 B B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {t} {s : statement B A2} :
  D.wellAnnotatedStatement A S G t s ->
  D.wellTypedStatement S G t s.
Proof.
  apply (
    statement_nrect
      (fun x => forall G (Hannot : D.wellAnnotatedStatement' A S G t x), D.wellTypedStatement' S G t x)
      (fun x => forall G (Hannot : D.wellAnnotatedStatement A S G t x), D.wellTypedStatement S G t x)
      (fun x => forall G (Hannot : allList (D.wellAnnotatedStatement A S G t) x), allList (D.wellTypedStatement S G t) x)
  ); intros; inversion_clear Hannot;
  econstructor (
  match goal with
  | |- D.typeable _ _ _ => eapply wellAnnotated_typeable; eassumption
  | |- D.typeOfRValue _ _ _ _ => eapply wellAnnotatedRValue_typeOfRValue; eassumption
  | |- D.assignable _ _ _ _ => eapply wellAnnotatedAssignee_assignable; eassumption
  | |- allList (D.wellTypedDefinition _ _) _ => eapply wellAnnotatedDeclaration_wellTypedDeclaration; eassumption
  | _ => eassumption || now firstorder
  end
  ).
Qed.

Lemma wellAnnotatedFunction_wellTypedFunction {A1 A2 B B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {p : _ * _ * statement B A2} :
  D.wellAnnotatedFunction A S p ->
  D.wellTypedFunction S p.
Proof.
  inversion_clear 1.
  econstructor.
  - assumption.
  - assumption.
  - assumption.
  - eapply wellAnnotatedStatement_wellTypedStatement; eassumption.
Qed.

Lemma wellAnnotatedSigma_wellTypedSigma {A1 A2 B} {A : annotation A1 A2} {S : sigma B A2} :
  D.wellAnnotatedSigma A S ->
  D.wellTypedSigma S.
Proof.
  intros Hannot v p Hlookup.
  exact (wellAnnotatedFunction_wellTypedFunction (Hannot v p Hlookup)).
Qed.

Lemma wellAnnotatedProgram_wellTypedProgram {A1 A2 B} {A : annotation A1 A2} {p : program B A2} :
  D.wellAnnotatedProgram A p ->
  D.wellTypedProgram p.
Proof.
  inversion_clear 1.
  econstructor.
  - eassumption.
  - eapply wellAnnotatedSigma_wellTypedSigma; eassumption. 
Qed.

(* Section 3: typing relation doesn't distinguish programs that are identical up to annotations *)

Lemma typeOfLValue_equiv_aux {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {e1 : expression A1} {e2 : expression A2} {q} {t}:
  (forall {e2 : expression A2} {gtc},
     D.equivExpression e1 e2 ->
     D.typeOfExpression S1 G e1 gtc ->
     D.typeOfExpression S2 G e2 gtc) ->
  D.equivSigma S1 S2 ->
  D.equivExpression e1 e2 ->
  D.typeOfLValue S1 G e1 q t ->
  D.typeOfLValue S2 G e2 q t.
Proof. inversion_clear 4; econstructor; firstorder. Qed.

Lemma typeOfRValue_equiv_aux {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {e1 : expression A1} {e2 : expression A2} {gt} :
  (forall {e2 : expression A2} {gtc},
     D.equivExpression e1 e2 ->
     D.typeOfExpression S1 G e1 gtc ->
     D.typeOfExpression S2 G e2 gtc) ->
  D.equivSigma S1 S2 ->
  D.equivExpression e1 e2 ->
  D.typeOfRValue S1 G e1 gt ->
  D.typeOfRValue S2 G e2 gt.
Proof.
  intros typeOfExpression_equiv.
  inversion_clear 3;
  econstructor (now repeat first [eassumption | eapply typeOfExpression_equiv | eapply typeOfLValue_equiv_aux]).
Qed.

Lemma assignable_equiv_aux {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {e2 : expression A1} {e2' : expression A2} {t1} :
  (forall {e2' : expression A2} {gtc},
     D.equivExpression e2 e2' ->
     D.typeOfExpression S1 G e2  gtc ->
     D.typeOfExpression S2 G e2' gtc) ->
  D.equivSigma S1 S2 ->
  D.equivExpression e2 e2' ->
  D.assignable S1 G t1 e2 ->
  D.assignable S2 G t1 e2'.
Proof.
  intros typeOfExpression_equiv.
  inversion_clear 3;
  econstructor (
    now repeat first [
      eassumption
    | eapply typeOfExpression_equiv
    | eapply typeOfRValue_equiv_aux
    | eapply nullPointerConstant_equiv
    ]
  ).
Qed.

Ltac typeOfExpression_equiv_tac S1 S2 :=
  match goal with
  | Hlookup     : D.lookup S1 _ _
  , HequivSigma : D.equivSigma S1 S2 |- D.typeOfExpression' S2 _ (Var _) (GenRValueType _) => destruct ((proj1 HequivSigma) _ _ Hlookup) as [? [? [? ?]]]; econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivExpression ?e1 _ -> D.typeOfExpression S1 _ ?e1 _ -> D.typeOfExpression S2 _ _ _
  , _  : D.equivExpression ?e1 ?e2 |- D.typeOfExpression S2 _ ?e2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfExpression S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivExpression' ?e1 _ -> D.typeOfExpression' S1 _ ?e1 _ -> D.typeOfExpression' S2 _ _ _
  , _  : D.equivExpression' ?e1 ?e2 |- D.typeOfExpression' S2 _ ?e2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfExpression' S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | IH : forall _ _, D.equivArguments ?es1 _ -> D.typeOfArguments S1 _ ?es1 _ -> D.typeOfArguments S2 _ _ _
  , _  : D.equivArguments ?es1 ?es2 |- D.typeOfArguments S2 _ ?es2 _ => eapply IH; now typeOfExpression_equiv_tac S1 S2
  | |- D.typeOfArguments S2 _ _ _ => econstructor (now typeOfExpression_equiv_tac S1 S2)
  | H : D.typeOfRValue _ _ ?e1' _
  , _  : D.equivExpression ?e1' ?e2' |- D.typeOfRValue _ _ ?e2' _ => eapply @typeOfRValue_equiv_aux with (e1:=e1'); eassumption
  | H : D.typeOfLValue _ _ ?e1' _ _
  , _  : D.equivExpression ?e1' ?e2' |- D.typeOfLValue _ _ ?e2' _ _ => eapply @typeOfLValue_equiv_aux with (e1:=e1'); eassumption
  | H : D.assignable _ _ _ ?e1'
  , _  : D.equivExpression ?e1' ?e2' |- D.assignable _ _ _ ?e2' => eapply @assignable_equiv_aux with (e2:=e1'); eassumption
  | |- D.nullPointerConstant _ => eapply nullPointerConstant_equiv; eassumption
  | _ : D.equivExpression ?e1 ?e2
  , H : ~ D.nullPointerConstant ?e1 |- ~ D.nullPointerConstant ?e2 => intros ?; apply H; eapply nullPointerConstant_equiv; [eapply equivExpression_symm; eassumption | assumption]
  | _ => solve [eassumption|reflexivity]
  | |- type_from_sigma _ = type_from_sigma _ => unfold type_from_sigma; congruence
  end.

Lemma typeOfExpression_equiv {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2} {t},
    D.equivExpression e1 e2 ->
    D.typeOfExpression S1 G e1 t ->
    D.typeOfExpression S2 G e2 t.
Proof.
  intros HequivSigma.
  apply (
    expression_nrect
      (fun x => forall (y : expression' A2) t (Hequiv : D.equivExpression' x y) (Ht1 : D.typeOfExpression' S1 G x t), D.typeOfExpression' S2 G y t)
      (fun x => forall y t (Hequiv : D.equivExpression x y) (Ht1 : D.typeOfExpression S1 G x t), D.typeOfExpression S2 G y t)
      (fun x => forall (y : list (expression A2)) p (Hequiv : D.equivArguments x y) (Ht1 : D.typeOfArguments S1 G x p), D.typeOfArguments S2 G y p)
  ); intros; inversion Hequiv; subst; inversion Ht1; subst;
  now typeOfExpression_equiv_tac S1 S2.
Qed.

Lemma typeable_equiv {A1 A2 B1 B1' B2 B2'} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {G}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2},
    D.equivExpression e1 e2 ->
    D.typeable S1 G e1 ->
    D.typeable S2 G e2.
Proof. inversion_clear 3. econstructor; eapply typeOfExpression_equiv; eassumption. Qed.

Lemma typeOfRValue_equiv {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {e1 : expression A1} {e2 : expression A2} {t},
    D.equivExpression e1 e2 ->
    D.typeOfRValue S1 G e1 t ->
    D.typeOfRValue S2 G e2 t.
Proof.
  intros;
  repeat first [
    eassumption
  | eapply typeOfRValue_equiv_aux
  | eapply typeOfExpression_equiv].
Qed.

Lemma assignable_equiv {A1 A2 B1 B1' B2 B2'} {G} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'}  :
  D.equivSigma S1 S2 ->
  forall {t1} {e2 : expression A1} {e2' : expression A2},
    D.equivExpression e2 e2' ->
    D.assignable S1 G t1 e2 ->
    D.assignable S2 G t1 e2'.
Proof.
  intros;
  repeat first [
    eassumption
  | eapply assignable_equiv_aux
  | eapply typeOfExpression_equiv].
Qed.

Lemma wellTypedDefinition_equiv {A1 A2 B1 B1' B2 B2'} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {G} :
  D.equivSigma S1 S2 ->
  forall {d1 : _ * expression A1} {d2 : _ * expression A2},
    D.equivDefinition d1 d2 ->
    D.wellTypedDefinition S1 G d1 ->
    D.wellTypedDefinition S2 G d2.
Proof.
  intros HequivSigma [].
  inversion_clear 1.
  inversion_clear 1.
  econstructor.
  * eassumption.
  * eapply assignable_equiv; eassumption.
Qed.

Lemma wellTypedDeclaration_equiv {A1 A2 B1 B1' B2 B2'} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {G} :
  D.equivSigma S1 S2 ->
  forall {ds1 : list (_ * expression A1)} {ds2 : list (_ * expression A2)},
    D.equivDeclaration ds1 ds2 ->
    allList (D.wellTypedDefinition S1 G) ds1 ->
    allList (D.wellTypedDefinition S2 G) ds2.
Proof.
  induction ds1;
  inversion_clear 1;
  inversion_clear 1;
  econstructor;
  solve [eassumption | eapply wellTypedDefinition_equiv; eassumption | eapply IHds1; eassumption].
Qed.

Lemma wellTypedStatement_equiv {A1 A1' A2 A2' B1 B1' B2 B2'} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} {G} :
  D.equivSigma S1 S2 ->
  forall {s1 : statement A1 A1'} {s2 : statement A2 A2'} {t_return},
    D.equivStatement s1 s2 ->
    D.wellTypedStatement S1 G t_return s1 ->
    D.wellTypedStatement S2 G t_return s2.
Proof.
  intros HequivSigma s1 s2 t_return.
  revert s1 s2 G.
  eapply (
    statement_nrect
      (fun x => forall (y : statement' A2 A2') G (Hequiv : D.equivStatement' x y) (Ht1 : D.wellTypedStatement' S1 G t_return x), D.wellTypedStatement' S2 G t_return y)
      (fun x => forall (y : statement A2 A2') G (Hequiv : D.equivStatement x y) (Ht1 : D.wellTypedStatement S1 G t_return x), D.wellTypedStatement S2 G t_return y)
      (fun x => forall (y : list (statement A2 A2')) G (Hequiv : D.equivBlock x y) (Ht1 : allList (D.wellTypedStatement S1 G t_return) x), allList (D.wellTypedStatement S2 G t_return) y)
  ); intros; inversion Hequiv; subst; inversion Ht1; subst;
  econstructor;
  match goal with
  | H : forall _ _, _ -> D.wellTypedStatement _ _ _ ?s1 -> _
  , _ : D.equivStatement ?s1 ?s2 |-  D.wellTypedStatement S2 _ _ ?s2 => eapply H; eassumption
  | H : forall _ _, _ -> D.wellTypedStatement' _ _ _ ?s1 -> _
  , _ : D.equivStatement' ?s1 ?s2 |-  D.wellTypedStatement' S2 _ _ ?s2 => eapply H; eassumption
  | H : forall _ _, _ -> allList (D.wellTypedStatement _ _ _) ?ss1 -> _
  , _ : D.equivBlock ?ss1 ?ss2 |-  allList (D.wellTypedStatement S2 _ _) ?ss2 => eapply H; eassumption
  | |- D.typeable     S2 _ _   => eapply typeable_equiv; eassumption
  | |- D.assignable   S2 _ _ _ => eapply assignable_equiv; eassumption
  | |- D.typeOfRValue S2 _ _ _ => eapply typeOfRValue_equiv; eassumption
  | |- D.freshBindings _ S2 => eapply AilTyping_proof.freshBindings_equivSigma; eassumption
  | |- allList (D.wellTypedDefinition S2 _) _ => eapply wellTypedDeclaration_equiv; eassumption
  | _ => eassumption
  end.
Qed.

Lemma wellTypedFunction_equiv {A1 A1' A2 A2' B1 B1' B2 B2': Set} {S1 : sigma B1 B1'} {S2 : sigma B2 B2'} :
  D.equivSigma S1 S2 ->
  forall {p1 : _ * statement A1 A1'} {p2 : _ * statement A2 A2'},
    D.equivFunction p1 p2 ->
    D.wellTypedFunction S1 p1 ->
    D.wellTypedFunction S2 p2.
Proof.
  intros HequivSigma [[? ?] ?] [[? ?] ?] [Heq ?].
  inversion_clear Heq.
  inversion_clear 1.
  econstructor.
  - assumption.
  - eapply AilTyping_proof.freshBindings_equivSigma; eassumption.
  - assumption.
  - eapply wellTypedStatement_equiv; eassumption.
Qed.

Lemma wellTypedSigma_equiv {A1 A1' A2 A2': Set} {S1 : sigma A1 A1'} {S2 : sigma A2 A2'} :
  D.equivSigma S1 S2 ->
  D.wellTypedSigma S1 ->
  D.wellTypedSigma S2.
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

Lemma wellTypedProgram_equiv {A1 A1' A2 A2': Set} :
  forall {p1 : program A1 A1'} {p2 : program A2 A2'},
    D.equivProgram p1 p2 ->
    D.wellTypedProgram p1 ->
    D.wellTypedProgram p2.
Proof.
  intros [? ?] [? ?] [Heq HequivSigma]; simpl in *; subst.
  inversion_clear 1.
  match goal with
  | H : D.lookup _ _ _ |- _ => destruct ((proj1 HequivSigma) _ _ H) as [[? ?] [? [? ?]]]; simpl in *; subst
  end.
  econstructor.
  - eassumption.
  - eapply wellTypedSigma_equiv; eassumption.
Qed.

Lemma equivExpression_wellAnnotatedExpression_typeOfExpression  {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 : expression A1} {e2 : expression A2} {gtc} :
  D.equivExpression e1 e2 ->
  D.wellAnnotatedExpression A S G e2 gtc ->
  D.typeOfExpression S G e1 gtc.
Proof.
  intros Hequiv Hannot.
  eapply typeOfExpression_equiv.
  apply equivSigma_refl.
  eapply equivExpression_symm; eassumption.
  eapply wellAnnotatedExpression_typeOfExpression; eassumption.
Qed.

Lemma equivExpression_wellAnnotatedRValue_typeOfRValue {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 : expression A1} {e2 : expression A2} {gt} :
  D.equivExpression e1 e2 ->
  D.wellAnnotatedRValue A S G e2 gt ->
  D.typeOfRValue S G e1 gt.
Proof.
  intros Hequiv Hannot.
  eapply typeOfRValue_equiv.
  apply equivSigma_refl.
  eapply equivExpression_symm; eassumption.
  eapply wellAnnotatedRValue_typeOfRValue; eassumption.
Qed.

Lemma typeOfExpression_wellAnnotatedExpression_neg  {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 : expression A1} :
  (forall gtc, ~ D.typeOfExpression S G e1 gtc) ->
  forall e2 gtc, D.equivExpression e1 e2 -> ~ D.wellAnnotatedExpression A S G e2 gtc.
Proof.
  intros Hfalse ? ? ? ?.
  eapply Hfalse.
  eapply equivExpression_wellAnnotatedExpression_typeOfExpression; eassumption.
Qed.

(* Section 4: well-annotation predicate for expressions in independent of annotations used in function environment sigma *)

Lemma wellAnnotatedLValue_equivSigma_aux {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {e : expression A2} {q} {t} :
  (forall {gtc},
     D.wellAnnotatedExpression A S  G e gtc ->
     D.wellAnnotatedExpression A S' G e gtc) ->
  D.equivSigma S S' ->
  D.wellAnnotatedLValue A S  G e q t ->
  D.wellAnnotatedLValue A S' G e q t.
Proof.
  intros wellAnnotatedExpression.
  inversion_clear 2.
  econstructor(solve [eassumption | eapply wellAnnotatedExpression; eassumption]).
Qed.

Lemma wellAnnotatedRValue_equivSigma_aux {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {e : expression A2} {gt} :
  (forall {gtc},
     D.wellAnnotatedExpression A S  G e gtc  ->
     D.wellAnnotatedExpression A S' G e gtc) ->
  D.equivSigma S S' ->
  D.wellAnnotatedRValue A S  G e gt ->
  D.wellAnnotatedRValue A S' G e gt.
Proof.
  intros wellAnnotatedExpression Hequiv.
  inversion_clear 1;
  econstructor (
    solve [
      eassumption
    | eapply wellAnnotatedExpression; eassumption
    | eapply (wellAnnotatedLValue_equivSigma_aux wellAnnotatedExpression Hequiv); eassumption
    ]
  ).
Qed.

Lemma wellAnnotatedAssignee_equivSigma_aux {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {t1} {e2 : expression A2} :
  (forall {gtc},
     D.wellAnnotatedExpression A S  G e2 gtc  ->
     D.wellAnnotatedExpression A S' G e2 gtc) ->
  D.equivSigma S S' ->
  D.wellAnnotatedAssignee A S  G t1 e2 ->
  D.wellAnnotatedAssignee A S' G t1 e2.
Proof.
  intros IH Hequiv.
  inversion_clear 1;
  econstructor (
  match goal with
  | IH : forall _, D.wellAnnotatedExpression _ _ _ ?e _ -> _ |- D.wellAnnotatedExpression _ _ _ ?e _ => eapply IH; eassumption
  | IH : forall _, D.wellAnnotatedExpression _ _ _ ?e _ -> _ |- D.wellAnnotatedLValue _ _ _ ?e _ _ => eapply (wellAnnotatedLValue_equivSigma_aux IH Hequiv); eassumption
  | IH : forall _, D.wellAnnotatedExpression _ _ _ ?e _ -> _ |- D.wellAnnotatedRValue _ _ _ ?e _ => eapply (wellAnnotatedRValue_equivSigma_aux IH Hequiv); eassumption
  | _ => eassumption
  end).
Qed.

Lemma wellAnnotatedExpression_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {e : expression A2} {gtc} :
  D.equivSigma S S' ->
  D.wellAnnotatedExpression A S  G e gtc ->
  D.wellAnnotatedExpression A S' G e gtc.
Proof.
  intros Hequiv.
  revert gtc.
  apply (
    expression_nrect
      (fun x => forall gtc (Hannot : D.wellAnnotatedExpression' A S G x gtc), D.wellAnnotatedExpression' A S' G x gtc)
      (fun x => forall gtc (Hannot : D.wellAnnotatedExpression  A S G x gtc), D.wellAnnotatedExpression  A S' G x gtc)
      (fun x => forall ps  (Hannot : D.wellAnnotatedArguments   A S G x ps ), D.wellAnnotatedArguments   A S' G x ps )
  ); intros; inversion_clear Hannot; try
  match goal with
  | Hlookup : D.lookup S _ ?p |- D.wellAnnotatedExpression' _ _ _ (Var _) _ =>
      let p' := fresh in
      let Hlookup' := fresh in
      let Hequiv' := fresh in
      destruct (proj1 Hequiv _ _ Hlookup) as [p' [Hlookup' Hequiv']];
      econstructor; [
        eexact Hlookup'
      | destruct p  as [[] ?];
        destruct p' as [[] ?];
        inversion Hequiv';
        unfold type_from_sigma in *;
        congruence
      ]
  | _ =>
      econstructor (
        match goal with
        | IH : forall _, D.wellAnnotatedExpression  _ _ _ ?e  _ -> _ |- D.wellAnnotatedExpression  _ _ _ ?e  _   => eapply IH; eassumption
        | IH : forall _, D.wellAnnotatedExpression' _ _ _ ?e  _ -> _ |- D.wellAnnotatedExpression' _ _ _ ?e  _   => eapply IH; eassumption
        | IH : forall _, D.wellAnnotatedArguments   _ _ _ ?es _ -> _ |- D.wellAnnotatedArguments   _ _ _ ?es _   => eapply IH; eassumption    
        | IH : forall _, D.wellAnnotatedExpression  _ _ _ ?e  _ -> _ |- D.wellAnnotatedLValue      _ _ _ ?e  _ _ => eapply (wellAnnotatedLValue_equivSigma_aux IH Hequiv); eassumption
        | IH : forall _, D.wellAnnotatedExpression  _ _ _ ?e  _ -> _ |- D.wellAnnotatedRValue      _ _ _ ?e  _   => eapply (wellAnnotatedRValue_equivSigma_aux IH Hequiv); eassumption
        | IH : forall _, D.wellAnnotatedExpression  _ _ _ ?e  _ -> _ |- D.wellAnnotatedAssignee    _ _ _ _   ?e  => eapply (wellAnnotatedAssignee_equivSigma_aux IH Hequiv); eassumption
        | _ => eassumption
        end
      )
  end.
Qed.

Lemma wellAnnotatedRValue_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {e : expression A2} {gt} :
  D.equivSigma S S' ->
  D.wellAnnotatedRValue A S  G e gt ->
  D.wellAnnotatedRValue A S' G e gt.
Proof.
  intros Hequiv.
  eapply (wellAnnotatedRValue_equivSigma_aux (fun gtc => wellAnnotatedExpression_equivSigma (gtc:=gtc) Hequiv) Hequiv).
Qed.

Lemma wellAnnotatedAssignee_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {t1} {e2 : expression A2} :
  D.equivSigma S S' ->
  D.wellAnnotatedAssignee A S  G t1 e2 ->
  D.wellAnnotatedAssignee A S' G t1 e2.
Proof.
  intros Hequiv.
  eapply (wellAnnotatedAssignee_equivSigma_aux (fun gtc => wellAnnotatedExpression_equivSigma (gtc:=gtc) Hequiv) Hequiv).
Qed.

Lemma wellAnnotated_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {e : expression A2} :
  D.equivSigma S S' ->
  D.wellAnnotated A S  G e ->
  D.wellAnnotated A S' G e.
Proof. inversion_clear 2; econstructor; eapply wellAnnotatedExpression_equivSigma; eassumption. Qed.

Lemma wellAnnotatedDefinition_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {d : _ * expression A2} :
  D.equivSigma S S' ->
  D.wellAnnotatedDefinition A S  G d ->
  D.wellAnnotatedDefinition A S' G d.
Proof.
  intros Heq.
  inversion_clear 1.
  econstructor.
  - eassumption.
  - eapply wellAnnotatedAssignee_equivSigma; eassumption.
Qed.

Lemma wellAnnotatedDeclaration_equivSigma {A1 A2 B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {ds : list (_ * expression A2)} :
  D.equivSigma S S' ->
  allList (D.wellAnnotatedDefinition A S  G) ds ->
  allList (D.wellAnnotatedDefinition A S' G) ds.
Proof.
  intros Heq.
  induction ds;
  inversion_clear 1;
  econstructor.
  - eapply wellAnnotatedDefinition_equivSigma; eassumption.
  - eapply IHds; eassumption.
Qed.

Lemma wellAnnotatedStatement_equivSigma {A1 A2 B B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {G} {t} {s : statement B A2} :
  D.equivSigma S S' ->
  D.wellAnnotatedStatement A S  G t s ->
  D.wellAnnotatedStatement A S' G t s.
Proof.
  intros Hequiv.
  apply (
    statement_nrect
      (fun x => forall G (Hannot : D.wellAnnotatedStatement' A S G t x), D.wellAnnotatedStatement' A S' G t x)
      (fun x => forall G (Hannot : D.wellAnnotatedStatement  A S G t x), D.wellAnnotatedStatement  A S' G t x)
      (fun x => forall G (Hannot : allList (D.wellAnnotatedStatement A S G t) x), allList (D.wellAnnotatedStatement A S' G t) x)
  ); intros; inversion_clear Hannot;
  econstructor (
    match goal with
    | IH : forall _, D.wellAnnotatedStatement  _ _ _ _ ?s -> _ |- D.wellAnnotatedStatement _ _ _ _ ?s => eapply IH; eassumption
    | IH : forall _, D.wellAnnotatedStatement' _ _ _ _ ?s -> _ |- D.wellAnnotatedStatement' _ _ _ _ ?s => eapply IH; eassumption
    | IH : forall _, allList (D.wellAnnotatedStatement _ _ _ _) ?ss -> _ |- allList (D.wellAnnotatedStatement _ _ _ _) ?ss => eapply IH; eassumption
    | |- D.wellAnnotated           _ _ _ ?e    => eapply (wellAnnotated_equivSigma Hequiv); eassumption
    | |- D.wellAnnotatedExpression _ _ _ ?e _  => eapply (wellAnnotatedExpression_equivSigma Hequiv); eassumption
    | |- D.wellAnnotatedRValue     _ _ _ ?e _  => eapply (wellAnnotatedRValue_equivSigma Hequiv); eassumption
    | |- D.wellAnnotatedAssignee   _ _ _ _  ?e => eapply (wellAnnotatedAssignee_equivSigma Hequiv); eassumption
    | |- D.freshBindings _ _ => eapply (AilTyping_proof.freshBindings_equivSigma Hequiv); assumption
    | |- allList (D.wellAnnotatedDefinition _ _ _) _ => eapply (wellAnnotatedDeclaration_equivSigma Hequiv); assumption
    | _ => eassumption
    end
  ).
Qed.  

Lemma wellAnnotatedFunction_equivSigma {A1 A2 B B1 B2 B1' B2' : Set} {A : annotation A1 A2} {S : sigma B1 B2} {S' : sigma B1' B2'} {p : _ * _ * statement B A2} :
  D.equivSigma S S' ->
  D.wellAnnotatedFunction A S  p ->
  D.wellAnnotatedFunction A S' p.
Proof.
  intros Hequiv.
  inversion_clear 1.
  econstructor.
  - assumption.
  - apply (AilTyping_proof.freshBindings_equivSigma Hequiv); assumption.
  - assumption.
  - apply (wellAnnotatedStatement_equivSigma Hequiv); assumption.
Qed.

(* Section 5: if one program is well-annotated so are programs that are identical up to annotations but agree on type annotations *)

Lemma wellAnnotatedLValue_equivAnnotation_aux {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {e2 : expression A2} {e2' : expression A2'} {q} {t} :
  (forall {gtc},
     D.equivAnnotationExpression A A' e2 e2' ->
     D.wellAnnotatedExpression A S G e2 gtc ->
     D.wellAnnotatedExpression A' S G e2' gtc) ->
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedLValue A  S G e2  q t ->
  D.wellAnnotatedLValue A' S G e2' q t.
Proof.
  intros wellAnnotatedExpression_equivAnnotation Hequiv.
  inversion_clear 1.
  econstructor; eapply wellAnnotatedExpression_equivAnnotation; eassumption.
Qed.

Lemma wellAnnotatedRValue_equivAnnotation_aux {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {e2 : expression A2} {e2' : expression A2'} {gt} :
  (forall {gtc},
     D.equivAnnotationExpression A A' e2 e2' ->
     D.wellAnnotatedExpression A  S G e2  gtc ->
     D.wellAnnotatedExpression A' S G e2' gtc) ->
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedRValue A  S G e2  gt ->
  D.wellAnnotatedRValue A' S G e2' gt.
Proof.
  intros wellAnnotatedExpression_equivAnnotation Hequiv.
  inversion_clear 1;
  econstructor (
    solve [
      eassumption
    | eapply wellAnnotatedExpression_equivAnnotation; eassumption
    | eapply (wellAnnotatedLValue_equivAnnotation_aux _ wellAnnotatedExpression_equivAnnotation); eassumption
    ]
  ).
Qed.

Lemma wellAnnotatedAssignee_equivAnnotation_aux {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {t1} {e2 : expression A2} {e2' : expression A2'} :
  (forall {gtc},
     D.equivAnnotationExpression A A' e2 e2' ->
     D.wellAnnotatedExpression A  S G e2  gtc ->
     D.wellAnnotatedExpression A' S G e2' gtc) ->
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedAssignee A  S G t1 e2 ->
  D.wellAnnotatedAssignee A' S G t1 e2'.
Proof.
  intros wellAnnotatedExpression_equivAnnotation Hequiv.
  inversion_clear 1;
  econstructor (
    solve [
      eassumption
    | eapply wellAnnotatedExpression_equivAnnotation; eassumption
    | eapply (wellAnnotatedLValue_equivAnnotation_aux _ wellAnnotatedExpression_equivAnnotation); eassumption
    | eapply (wellAnnotatedRValue_equivAnnotation_aux _ wellAnnotatedExpression_equivAnnotation); eassumption
    | eapply nullPointerConstant_equiv; [eapply equivAnnotationExpression_equivExpression; eassumption | assumption]
    ]
  ).
Qed.

Lemma wellAnnotatedExpression_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {e2 : expression A2} {e2' : expression A2'} {gtc} :
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedExpression A  S G e2  gtc ->
  D.wellAnnotatedExpression A' S G e2' gtc.
Proof.
  revert e2' gtc.
  apply (
    expression_nrect
      (fun x => forall y gtc (Hequiv : D.equivAnnotationExpression' A A' x y) (Hannot : D.wellAnnotatedExpression' A S G x gtc), D.wellAnnotatedExpression' A' S G y gtc)
      (fun x => forall y gtc (Hequiv : D.equivAnnotationExpression A A' x y) (Hannot : D.wellAnnotatedExpression A S G x gtc), D.wellAnnotatedExpression A' S G y gtc)
      (fun x => forall y p (Hequiv : D.equivAnnotationArguments A A' x y) (Hannot : D.wellAnnotatedArguments A S G x p), D.wellAnnotatedArguments A' S G y p)
  ); intros; inversion Hequiv; subst; inversion Hannot; subst; try
  econstructor (
  match goal with
  | IH : forall _ _, D.equivAnnotationExpression A A' ?e1 _ -> _
  , Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedExpression A' S G ?e2 _ =>
      eapply (IH _ _ Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationExpression' A A' ?e1 _ -> _
  , Hequiv : D.equivAnnotationExpression' A A' ?e1 ?e2 |- D.wellAnnotatedExpression' A' S G ?e2 _ =>
      eapply (IH _ _ Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationArguments A A' ?es1 _ -> _
  , Hequiv : D.equivAnnotationArguments A A' ?es1 ?es2 |- D.wellAnnotatedArguments A' S G ?es2 _ =>
      eapply (IH _ _ Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationExpression A A' ?e1 _ -> _
  , Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedRValue A' S G ?e2 _ =>
      eapply (wellAnnotatedRValue_equivAnnotation_aux A' (IH _) Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationExpression A A' ?e1 _ -> _
  , Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedLValue A' S G ?e2 _ _ =>
      eapply (wellAnnotatedLValue_equivAnnotation_aux A' (IH _) Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationExpression A A' ?e1 _ -> _
  , Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedAssignee A' S G _ ?e2 =>
      eapply (wellAnnotatedAssignee_equivAnnotation_aux A' (IH _) Hequiv); eassumption
  | Hnull : D.nullPointerConstant ?e1
  , Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.nullPointerConstant ?e2 =>
      eapply (nullPointerConstant_equiv (equivAnnotationExpression_equivExpression Hequiv) Hnull)
  | H : ~ D.nullPointerConstant ?e1, HequivAnnot : D.equivAnnotationExpression _ _ ?e1 ?e2 |- ~ D.nullPointerConstant ?e2 =>
      let Hnull := fresh in
      intros Hnull; apply H;
      now apply (nullPointerConstant_equiv (equivExpression_symm (equivAnnotationExpression_equivExpression HequivAnnot)) Hnull)
  | _ => eassumption || congruence
  end).
Qed.

Lemma wellAnnotatedRValue_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {e2 : expression A2} {e2' : expression A2'} {gt} :
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedRValue A  S G e2  gt ->
  D.wellAnnotatedRValue A' S G e2' gt.
Proof.
  intros Hequiv.
  eapply (wellAnnotatedRValue_equivAnnotation_aux A' (fun _ => wellAnnotatedExpression_equivAnnotation A') Hequiv).
Qed.

Lemma wellAnnotatedAssignee_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {t1} {e2 : expression A2} {e2' : expression A2'} :
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotatedAssignee A  S G t1 e2 ->
  D.wellAnnotatedAssignee A' S G t1 e2'.
Proof.
  intros Hequiv.
  eapply (wellAnnotatedAssignee_equivAnnotation_aux A' (fun _ => wellAnnotatedExpression_equivAnnotation A') Hequiv).
Qed.

Lemma wellAnnotated_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {e2 : expression A2} {e2' : expression A2'} :
  D.equivAnnotationExpression A A' e2 e2' ->
  D.wellAnnotated A  S G e2 ->
  D.wellAnnotated A' S G e2'.
Proof.
  intros HequivAnnot Hannot.
  inversion_clear Hannot.
  econstructor.
  eapply (wellAnnotatedExpression_equivAnnotation A' HequivAnnot); eassumption.
Qed.

Lemma wellAnnotatedDefinition_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {d2 : _ * expression A2} {d2' : _ * expression A2'} :
  D.equivAnnotationDefinition A A' d2 d2' ->
  D.wellAnnotatedDefinition A  S G d2 ->
  D.wellAnnotatedDefinition A' S G d2'.
Proof.
  inversion_clear 1;
  inversion_clear 1.
  econstructor.
  - eassumption.
  - eapply wellAnnotatedAssignee_equivAnnotation; eassumption.
Qed.

Lemma wellAnnotatedDeclaration_equivAnnotation {A1 A2 A2' B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {ds2 : list (_ * expression A2)} {ds2' : list (_ * expression A2')} :
  D.equivAnnotationDeclaration A A' ds2 ds2' ->
  allList (D.wellAnnotatedDefinition A  S G) ds2 ->
  allList (D.wellAnnotatedDefinition A' S G) ds2'.
Proof.
  revert ds2'.
  induction ds2;
  inversion_clear 1;
  inversion_clear 1;
  econstructor.
  - eapply wellAnnotatedDefinition_equivAnnotation; eassumption.
  - eapply IHds2; eassumption.
Qed.

Lemma wellAnnotatedStatement_equivAnnotation {A1 A2 A2' B B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {G} {t} {s2 : statement B A2} {s2' : statement B A2'} :
  D.equivAnnotationStatement A A' s2 s2' ->
  D.wellAnnotatedStatement A  S G t s2 ->
  D.wellAnnotatedStatement A' S G t s2'.
Proof.
  revert s2' G.
  apply (
    statement_nrect
      (fun x => forall (y : statement' B A2') G (HequivAnnot : D.equivAnnotationStatement' A A' x y) (Hannot : D.wellAnnotatedStatement' A S G t x), D.wellAnnotatedStatement' A' S G t y)
      (fun x => forall y G (HequivAnnot : D.equivAnnotationStatement A A' x y) (Hannot : D.wellAnnotatedStatement A S G t x), D.wellAnnotatedStatement A' S G t y)
      (fun x => forall (y : list (statement B A2')) G (HequivAnnot : D.equivAnnotationBlock A A' x y) (Hannot : allList (D.wellAnnotatedStatement A S G t) x), allList (D.wellAnnotatedStatement A' S G t) y)
  ); intros; inversion_clear HequivAnnot; inversion_clear Hannot;
  econstructor (
  match goal with
  | IH : forall _ _, D.equivAnnotationStatement' A A' ?s1 _ -> _
  , Hequiv : D.equivAnnotationStatement' A A' ?s1 ?s2 |- D.wellAnnotatedStatement' A' S _ _ ?s2 =>
      eapply (IH _ _ Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationStatement A A' ?s1 _ -> _
  , Hequiv : D.equivAnnotationStatement A A' ?s1 ?s2 |- D.wellAnnotatedStatement A' S _ _ ?s2 =>
      eapply (IH _ _ Hequiv); eassumption
  | IH : forall _ _, D.equivAnnotationBlock A A' ?ss1 _ -> _
  , Hequiv : D.equivAnnotationBlock A A' ?ss1 ?ss2 |- allList (D.wellAnnotatedStatement A' S _ _) ?ss2 =>
      eapply (IH _ _ Hequiv); eassumption
  | Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotated A' S _ ?e2 =>
      eapply (wellAnnotated_equivAnnotation A' Hequiv); eassumption
  | Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedRValue A' S _ ?e2 _ =>
      eapply (wellAnnotatedRValue_equivAnnotation A' Hequiv); eassumption
  | Hequiv : D.equivAnnotationExpression A A' ?e1 ?e2 |- D.wellAnnotatedAssignee A' S _ _ ?e2 =>
      eapply (wellAnnotatedAssignee_equivAnnotation A' Hequiv); eassumption
  | Hequiv : D.equivAnnotationDeclaration A A' ?ds1 ?ds2 |- allList (D.wellAnnotatedDefinition A' S _) ?ds2 =>
      eapply (wellAnnotatedDeclaration_equivAnnotation A' Hequiv); eassumption
  | _ => eassumption || congruence
  end).
Qed.

Lemma wellAnnotatedFunction_equivAnnotation {A1 A2 A2' B B1 B2 : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S : sigma B1 B2} {p2 : _ * _ * statement B A2} {p2' : _ * _ * statement B A2'} :
  D.equivAnnotationFunction A A' p2 p2' ->
  D.wellAnnotatedFunction A  S p2 ->
  D.wellAnnotatedFunction A' S p2'.
Proof.
  destruct p2  as [[t b] ?].
  destruct p2' as [[] ?].
  inversion_clear 1.
  inversion_clear 1.
  Tactics.subst_no_fail; Tactics.autoinjections.
  econstructor (solve [assumption | eapply wellAnnotatedStatement_equivAnnotation; eassumption]).
Qed.

Lemma wellAnnotatedSigma_equivAnnotation {A1 A2 A2' B : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {S2 : sigma B A2} {S2' : sigma B A2'} :
  D.equivAnnotationSigma A A' S2 S2' ->
  D.wellAnnotatedSigma A  S2 ->
  D.wellAnnotatedSigma A' S2'.
Proof.
  intros HequivAnnot Hannot.
  intros v p2' Hlookup2'.
  destruct (proj2 HequivAnnot v p2' Hlookup2') as [p2 [Hlookup2 HequivAnnotFunction]].
  pose proof (Hannot v p2 Hlookup2) as HannotFunction.
  apply (wellAnnotatedFunction_equivAnnotation A' HequivAnnotFunction).
  apply (wellAnnotatedFunction_equivSigma (equivAnnotationSigma_equivSigma HequivAnnot)).
  exact HannotFunction.
Qed.

Lemma wellAnnotatedProgram_equivAnnotation {A1 A2 A2' B : Set} {A : annotation A1 A2} (A' : annotation A1 A2') {p2 : program B A2} {p2' : program B A2'} :
  D.equivAnnotationProgram A A' p2 p2' ->
  D.wellAnnotatedProgram A  p2 ->
  D.wellAnnotatedProgram A' p2'.
Proof.
  destruct p2  as [].
  destruct p2' as [].
  inversion_clear 1.
  inversion_clear 1.
  simpl in *; Tactics.subst_no_fail; Tactics.autoinjections.
  destruct (proj1 (equivAnnotationSigma_equivSigma H1) _ _ H2) as [[] []].
  inversion H0.
  simpl in *; Tactics.subst_no_fail; Tactics.autoinjections.

  econstructor.
  - eassumption.
  - eapply wellAnnotatedSigma_equivAnnotation; eassumption.
Qed.

(* Section 6: type annotation algorithm respects relational specification *)

Ltac genType_neg_tac :=
  GenTypesAux_proof.genType_neg_tac ||
  match goal with
  | H : D.wellTypedBinaryArithmetic ?gt1 _ _, Hfalse : ~ D.arithmetic ?gt1 |- _ => exfalso; apply Hfalse; inversion_clear H; assumption
  | H : D.wellTypedBinaryArithmetic _ _ ?gt2, Hfalse : ~ D.arithmetic ?gt2 |- _ => exfalso; apply Hfalse; inversion_clear H; assumption
  | H : D.wellTypedBinaryArithmetic ?gt1 _ _, Hfalse : ~ D.integer ?gt1 |- _ => exfalso; apply Hfalse; inversion_clear H; assumption
  | H : D.wellTypedBinaryArithmetic _ _ ?gt2, Hfalse : ~ D.integer ?gt2 |- _ => exfalso; apply Hfalse; inversion_clear H; assumption
  end.

Ltac genType_elaborate_tac :=
  match goal with
  | H : D.void ?gt |- _ => is_var gt; inversion H; subst
  | H : D.pointer ?gt |- _ => is_var gt; inversion H; subst
  | H : D.wellTypedBinaryArithmetic (GenPointer _ _) _ _ |- _ => inversion_clear H
  | H : D.wellTypedBinaryArithmetic _ _ (GenPointer _ _) |- _ => inversion_clear H
  end.

Ltac genType_tac :=
  repeat first [genType_neg_tac | AilTyping_proof.types_neg_tac | genType_elaborate_tac | AilTyping_proof.types_elaborate_tac | finish fail].

Definition annotate_expression'_spec {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) G (e1 : expression' A1) :=
  match annotate_expression' A S G e1 with
  | Some (e2, gtc) =>
      D.equivExpression' e1 e2 /\
      D.wellAnnotatedExpression' A S G e2 gtc /\
      (forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gtc',
         D.equivExpression' e1 e2' ->
         D.wellAnnotatedExpression' A' S G e2' gtc' ->
         gtc = gtc')
  | None    =>
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gtc',
        D.equivExpression' e1 e2' ->
        ~ D.wellAnnotatedExpression' A' S G e2' gtc'
  end.

Definition annotate_expression_spec {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) G (e1 : expression A1) :=
  match annotate_expression A S G e1 with
  | Some e2 =>
      D.equivExpression e1 e2 /\
      D.wellAnnotatedExpression A S G e2 (type_of A e2) /\
      (forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gtc',
         D.equivExpression e1 e2' ->
         D.wellAnnotatedExpression A' S G e2' gtc' ->
         type_of A e2 = gtc')
  | None    =>
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gtc',
        D.equivExpression e1 e2' ->
        ~ D.wellAnnotatedExpression A' S G e2' gtc'
  end.

Definition annotate_arguments_spec {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) G (es1 : list (expression A1)) :=
  forall ps,
    match annotate_arguments A S G es1 ps with
    | Some es2 =>
        D.equivArguments es1 es2 /\
        D.wellAnnotatedArguments A S G es2 ps
    | None     =>
        forall {A1' A2' : Set} {A' : annotation A1' A2'} es2',
          D.equivArguments es1 es2' ->
          ~ D.wellAnnotatedArguments A' S G es2' ps
    end.

Definition annotate_assignee_spec {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) G t1 (e2 : expression A1) :=
  match annotate_assignee A S G t1 e2 with
  | Some e2' =>
      D.equivExpression e2 e2' /\
      D.wellAnnotatedAssignee A S G t1 e2'      
  | None     =>
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e2',
        D.equivExpression e2 e2' ->
        ~ D.wellAnnotatedAssignee A' S G t1 e2'
  end.

Definition annotate_rvalue_spec {A1 A2 B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) G (e1 : expression A1) :=
  match annotate_rvalue A S G e1 with
  | Some (e2, gt) =>
      D.equivExpression e1 e2 /\
      D.wellAnnotatedRValue A S G e2 gt /\
      (forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gt',
         D.equivExpression e1 e2' ->
         D.wellAnnotatedRValue A' S G e2' gt' ->
         gt = gt')
  | None    =>
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gtc',
        D.equivExpression e1 e2' ->
        ~ D.wellAnnotatedRValue A' S G e2' gtc'
  end.

Lemma annotate_rvalue_correct_aux {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_rvalue_spec A S G e1.
Proof.
  intros annotate_expression_correct.
  unfold annotate_rvalue_spec.
  unfold annotate_rvalue.
  unfold annotate_rvalue_aux.
  unfold option_bind.
  unfold annotate_expression_spec in annotate_expression_correct.
  destruct (annotate_expression A S G e1);
  repeat match goal with
  | |- context[type_of ?A ?e] => destruct (type_of A e)
  | |- AilTypesAux.lvalue_conversion ?t = _ -> _ => case_fun (AilTypesAux_proof.lvalue_conversion_correct t)
  | |- context[pointer_conversion ?gt] => notHyp (D.pointerConversion gt (pointer_conversion gt)); let H := fresh in pose proof (pointer_conversion_correct gt) as H; unfold findSpec in H
  | _ => context_destruct
  | H : _ /\ _ |- _ => intuition
  | |- D.wellAnnotatedRValue _ _ _ _ _  => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  intuition;
  repeat match goal with
  | H : D.wellAnnotatedLValue _ _ _ _ _ _ |- _ => inversion_clear H
  | H : D.wellAnnotatedRValue _ _ _ _ _ |- _ => inversion_clear H
  end;
  repeat match goal with
  | Hunique : forall _ _ _ _ _, D.equivExpression ?e1 _ -> _ -> ?gt1 = _
  , Hequiv  : D.equivExpression ?e1 ?e2
  , H : D.wellAnnotatedExpression _ _ _ ?e2 ?gt2 |- _ =>
      notSame gt1 gt2;
      pose proof (Hunique _ _ _ _ _ Hequiv H);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : AilTypesAux_defns.lvalueConversion ?t1 ?t2
  , H2 : AilTypesAux_defns.lvalueConversion ?t1 ?t2' |- _ =>
      notSame t2 t2';
      pose proof (AilTypesAux_proof.lvalueConversion_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.pointerConversion ?gt1 ?gt2
  , H2 : D.pointerConversion ?gt1 ?gt2' |- _ =>
      notSame gt2 gt2';
      pose proof (pointerConversion_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  solve [reflexivity | eapply annotate_expression_correct; eassumption | now firstorder].
Qed.

Lemma annotate_assignee_correct_aux {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {t1} {e2 : expression A1} :
  annotate_expression_spec A S G e2 ->
  annotate_assignee_spec A S G t1 e2.
Proof.
  intros annotate_rvalue_correct.
  unfold annotate_assignee_spec.
  unfold annotate_assignee.
  unfold annotate_assignee_aux.
  unfold option_bind.
  unfold well_typed_assignment.
  unfold andb.
  unfold orb.
  apply annotate_rvalue_correct_aux in annotate_rvalue_correct.
  unfold annotate_rvalue_spec in annotate_rvalue_correct.
  destruct (annotate_rvalue A S G e2);
  repeat match goal with
  | |- arithmetic ?t = _  -> _ => case_fun (arithmetic_correct t)
  | |- AilTypesAux.arithmetic ?t = _  -> _ => case_fun (AilTypesAux_proof.arithmetic_correct t)
  | |- null_pointer_constant ?e2 = _ -> _ => case_fun (null_pointer_constant_correct e2)
  | |- AilTypesAux.compatible ?t1 ?t2 = _  -> _ => case_fun (AilTypesAux_proof.compatible_correct t1 t2)
  | |- AilTypesAux.boolean ?t = _  -> _ => case_fun (AilTypesAux_proof.boolean_correct t)
  | |- AilTypesAux.void ?t = _  -> _ => case_fun (AilTypesAux_proof.void_correct t)
  | |- AilTypesAux.object ?t = _  -> _ => case_fun (AilTypesAux_proof.object_correct t)
  | |- AilTypesAux.sub_qualifiers ?q1 ?q2 = ?o -> _ => destruct o; intros ?
  | _ => context_destruct
  end;
  match goal with
  | |- _ /\ _ => intuition; econstructor (solve [econstructor (eassumption) | eassumption])
  | _ : forall _ _ _ _ _, _ -> ~ _ |- _ => inversion_clear 2; intuition; eapply annotate_rvalue_correct; eassumption
  | |- forall _ _ _ _, _ -> ~ _ =>
      inversion_clear 2; intuition;
      match goal with
      | H1 : D.nullPointerConstant ?e1 -> False
      , H2 : D.nullPointerConstant ?e3
      , Hequiv1 : D.equivExpression ?e2 ?e1
      , Hequiv2 : D.equivExpression ?e2 ?e3 |- False =>
          apply H1; exact (nullPointerConstant_equiv (equivExpression_trans (equivExpression_symm Hequiv2) Hequiv1) H2)
      | Hunique : forall _ _ _ _ _, _ -> _ -> ?gt1 = _
      , Hequiv : D.equivExpression e2 ?e2'
      , H : D.wellAnnotatedRValue _ S G ?e2' ?gt2 |- _ =>
          notSame gt1 gt2;
          pose proof (Hunique _ _ _ _ _ Hequiv H);
          Tactics.subst_no_fail; Tactics.autoinjections
      | _ => idtac
      end; now genType_tac
  end.
Qed.

Lemma well_typed_binary_arithmetic_correct gt1 aop gt2 :
  boolSpec (well_typed_binary_arithmetic gt1 aop gt2) (D.wellTypedBinaryArithmetic gt1 aop gt2).
Proof.
  do 2 unfold_goal.
  unfold andb.
  repeat match goal with
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- integer    ?gt = _ -> _ => case_fun (integer_correct    gt)
  | _ => context_destruct
  end; solve [constructor; assumption | inversion_clear 1; my_auto].
Qed.

Lemma well_typed_equality_correct {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} {e1' e2' : expression A2} {aop} {gt1 gt2} :
  D.equivExpression e1 e1' ->
  D.equivExpression e2 e2' ->
  D.wellAnnotatedRValue A S G e1' gt1 ->
  D.wellAnnotatedRValue A S G e2' gt2 ->
  (forall {A1' A2' : Set} {A' : annotation A1' A2'} e1' gt1',
     D.equivExpression e1 e1' ->
     D.wellAnnotatedRValue A' S G e1' gt1' ->
     gt1 = gt1') ->
  (forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gt2',
     D.equivExpression e2 e2' ->
     D.wellAnnotatedRValue A' S G e2' gt2' ->
     gt2 = gt2') ->
  (aop = Eq) \/ (aop = Ne) ->
  if well_typed_equality gt1 gt2 (null_pointer_constant e1') (null_pointer_constant e2') then
    D.wellAnnotatedExpression' A S G (Binary e1' aop e2') (GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
  else
    forall {A1' A2' : Set} {A' : annotation A1' A2'} e1' e2' gtc,
      D.equivExpression e1 e1' ->
      D.equivExpression e2 e2' ->
      ~ D.wellAnnotatedExpression' A' S G (Binary e1' aop e2') gtc.
Proof.
  intros Hequiv1 Hequiv2 H1 H2 wellAnnotatedRValue_unique1 wellAnnotatedRValue_unique2 Haop.
  unfold_goal.
  unfold andb.
  unfold orb.
  repeat match goal with
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- pointer ?gt = _ -> _ => case_fun (pointer_correct gt)
  | |- null_pointer_constant ?e = _ -> _ => case_fun (null_pointer_constant_correct e)
  | |- pointer_to_complete_object ?t = _ -> _ => case_fun_tac (pointer_to_complete_object_correct t) autodestruct id_tac
  | |- pointer_to_void ?t = _ -> _ => case_fun_tac (pointer_to_void_correct t) autodestruct id_tac
  | |- pointer_to_object ?t = _ -> _ => case_fun_tac (pointer_to_object_correct t) autodestruct id_tac
  | |- pointers_to_compatible_complete_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_complete_objects_correct t1 t2) autodestruct id_tac
  | |- pointers_to_compatible_objects ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct t1 t2) autodestruct id_tac
  | |- pointers_to_compatible_types ?t1 ?t2 = _ -> _ => case_fun_tac (pointers_to_compatible_types_correct t1 t2) autodestruct id_tac
  | |- AilTypesAux.compatible ?t1 ?t2 = ?o -> _ => case_fun (AilTypesAux_proof.compatible_correct t1 t2)
  | _ => context_destruct
  | _ => destruct Haop; subst aop
  | H : AilTypesAux.complete ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.complete _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | H : AilTypesAux.object   ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.object   _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q1 Void = GenPointer _ _ -> ~ AilTypesAux_defns.void _ |- False => now eapply (Hfalse q1 Void eq_refl AilTypesAux_defns.Void_Void)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ ->
                             GenPointer ?q2 ?t2 = _ ->
                             ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | |- D.wellAnnotatedExpression' _ S G _ _ => genType_tac; econstructor (finish eassumption)
  | H : _ \/ _ |- D.wellAnnotatedExpression' S G _ _ => destruct H as [? | ?]
  end;
  genType_tac;
  abstract (
  match goal with
  | |- forall _ _ _ _ _ _, _ -> _ -> ~ _ => inversion_clear 3
  end;
  repeat match goal with
  | H : D.wellAnnotatedRValue _ S G ?e' ?gt'
  , Hequiv : D.equivExpression ?e ?e'
  , Hunique : forall _ _ _ _ _, D.equivExpression ?e _ -> _ -> ?gt = _ |- _ => notSame gt gt'; pose proof (Hunique _ _ _ _ _ Hequiv H); Tactics.subst_no_fail; Tactics.autoinjections
  | H : AilTypesAux_defns.complete ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.complete _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | H : AilTypesAux_defns.object ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.object _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q1 Void = GenPointer _ _ -> ~ AilTypesAux_defns.object _ |- False => now eapply (Hfalse q1 Void eq_refl AilTypesAux_defns.Object_Void)
  | Hfalse : forall _ _, GenPointer ?q1 Void = GenPointer _ _ -> ~ AilTypesAux_defns.void _ |- False => now eapply (Hfalse q1 Void eq_refl AilTypesAux_defns.Void_Void)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ ->
                             GenPointer ?q2 ?t2 = _ ->
                             ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | H1 : ~ D.nullPointerConstant ?e1
  , H2 : D.nullPointerConstant ?e2
  , Hequiv1 : D.equivExpression ?e ?e1
  , Hequiv2 : D.equivExpression ?e ?e2 |- False => apply H1; exact (nullPointerConstant_equiv (equivExpression_trans (equivExpression_symm Hequiv2) Hequiv1) H2)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end).
Qed.

Lemma composite_pointer_correct gt1 gt2 :
  match composite_pointer gt1 gt2 with
  | Some gt =>
      exists q1' t1' q2' t2' t',
           gt1 = GenPointer  q1' t1'
        /\ gt2 = GenPointer  q2' t2'
        /\ gt  = GenPointer (AilTypesAux.combine_qualifiers q1' q2') t'
        /\ AilTypesAux_defns.compatible t1' t2'
        /\ AilTypesAux_defns.composite  t1' t2' t'
  | None   =>
      ~ D.pointer gt1 \/
      ~ D.pointer gt2 \/
      exists q1' t1' q2' t2',
           gt1 = GenPointer q1' t1'
        /\ gt2 = GenPointer q2' t2'
        /\ ~ AilTypesAux_defns.compatible t1' t2'
  end.
Proof.
  unfold_goal;
  unfold option_map.
  repeat match goal with
  | [|- AilTypesAux.composite ?t1 ?t2 = _ -> _] => case_fun (AilTypesAux_proof.composite_correct t1 t2)
  | [|- AilTypesAux.compatible ?t1 ?t2 = _ -> _] => case_fun (AilTypesAux_proof.compatible_correct t1 t2)
  | [|- ~ _ \/ _ \/ _] => solve [ left; inversion 1
                                | right; left; inversion 1
                                | repeat first [right; right | eexists | assumption]]
  | _ => context_destruct
  | [|- exists _ , _] => repeat first [eexists | split | reflexivity | assumption]
  | [H : AilTypesAux_defns.compatible ?t1 ?t2, Hfind : forall _, ~ AilTypesAux_defns.composite ?t1 ?t2 _ |- _] => destruct (AilTyping_proof.compatible_composite H Hfind)
  end.
Qed.

Lemma nullPointerConstant_wellAnnotatedExpression {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e : expression A2} {gtc} :
  D.nullPointerConstant e ->
  D.wellAnnotatedExpression A S G e gtc ->
  gtc = GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))) \/
  gtc = GenRValueType (GenPointer no_qualifiers Void).
Proof.
  apply (
    expression_nrect
      (fun e =>
         forall gtc (Hnull : D.nullPointerConstant' e) (Hannot : D.wellAnnotatedExpression' A S G e gtc),
           gtc = GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))) \/
           gtc = GenRValueType (GenPointer no_qualifiers Void))
      (fun e =>
         forall gtc (Hnull : D.nullPointerConstant e) (Hannot : D.wellAnnotatedExpression A S G e gtc),
           gtc = GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))) \/
           gtc = GenRValueType (GenPointer no_qualifiers Void))
      (fun _ => True));
  intros;
  trivial;
  inversion Hnull; subst;
  inversion_clear Hannot;
  repeat match goal with
  | H : AilTypesAux_defns.unqualified ?q |- _ =>
      is_var q; inversion H; subst
  | H : D.typeOfConstant _ ?git |- _ =>
      is_var git;
      pose proof (typeOfConstant_functional (type_of_constant_correct (0, None)) H);
      Tactics.subst_no_fail;
      Tactics.autoinjections
  end; now my_auto.
Qed.

Lemma nullPointerConstant_wellAnnotatedRValue {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e : expression A2} {gt} :
  D.nullPointerConstant e ->
  D.wellAnnotatedRValue A S G e gt ->
  gt = GenBasic (GenInteger (Concrete (Signed Int))) \/ gt = GenPointer no_qualifiers Void.
Proof.
  intros Hequiv.
  inversion_clear 1;
  repeat match goal with
  | H : D.wellAnnotatedLValue A S G e _ _ |- _ => inversion_clear H
  end;
  match goal with
  | H :  D.wellAnnotatedExpression A S G e _ |- _ => pose proof (nullPointerConstant_wellAnnotatedExpression Hequiv H)
  end;
  intuition; Tactics.subst_no_fail; Tactics.autoinjections;
  match goal with
  | H : D.pointerConversion _ _ |- _ => inversion H; now my_auto
  end.
Qed.

Lemma well_typed_conditional_correct_aux {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {gt1 gt2 gt3} {e1 e2 e3 : expression A1} {e1' e2' e3' : expression A2} :
  D.equivExpression e1 e1' ->
  D.equivExpression e2 e2' ->
  D.equivExpression e3 e3' ->
  D.wellAnnotatedRValue A S G e1' gt1 ->
  D.wellAnnotatedRValue A S G e2' gt2 ->
  D.wellAnnotatedRValue A S G e3' gt3 ->
  (forall {A1' A2' : Set} {A' : annotation A1' A2'} e1' gt1',
     D.equivExpression e1 e1' ->
     D.wellAnnotatedRValue A' S G e1' gt1' ->
     gt1 = gt1') ->
  (forall {A1' A2' : Set} {A' : annotation A1' A2'} e2' gt2',
     D.equivExpression e2 e2' ->
     D.wellAnnotatedRValue A' S G e2' gt2' ->
     gt2 = gt2') ->
  (forall {A1' A2' : Set} {A' : annotation A1' A2'} e3' gt3',
     D.equivExpression e3 e3' ->
     D.wellAnnotatedRValue A' S G e3' gt3' ->
     gt3 = gt3') ->
  match well_typed_conditional gt1 gt2 gt3 (null_pointer_constant e2') (null_pointer_constant e3') with
  | Some gtc =>
      D.wellAnnotatedExpression' A S G (Conditional e1' e2' e3') gtc /\
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e1' e2' e3' gtc',
        D.equivExpression e1 e1' ->
        D.equivExpression e2 e2' ->
        D.equivExpression e3 e3' ->
        D.wellAnnotatedExpression' A' S G (Conditional e1' e2' e3') gtc' ->
        gtc = gtc'
  | None     =>
      forall {A1' A2' : Set} {A' : annotation A1' A2'} e1' e2' e3' gtc',
         D.equivExpression e1 e1' ->
         D.equivExpression e2 e2' ->
         D.equivExpression e3 e3' ->
         ~ D.wellAnnotatedExpression' A' S G (Conditional e1' e2' e3') gtc'
  end.
Proof.
  intros Hequiv1 Hequiv2 Hequiv3 ? ? ? wellAnnotatedRValue_functional1 wellAnnotatedRValue_functional2 wellAnnotatedRValue_functional3.
  do 2 unfold_goal.
  destruct gt1, gt2, gt3; simpl;
  unfold andb;
  unfold option_map;
  unfold option_bind;
  unfold combine_qualifiers_left;
  unfold combine_qualifiers_right;
  repeat match goal with
  | |- scalar ?gt = _ -> _ => case_fun (scalar_correct gt)
  | |- AilTypesAux.object ?t = _ -> _ => case_fun (AilTypesAux_proof.object_correct t)
  | |- AilTypesAux.compatible ?t1 ?t2 = _ -> _ => case_fun (AilTypesAux_proof.compatible_correct t1 t2)
  | |- AilTypesAux.composite ?t1 ?t2 = _ -> _ => case_fun (AilTypesAux_proof.composite_correct t1 t2)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | |- void ?gt = _ -> _ => case_fun (void_correct gt)
  | |- pointer ?gt = _ -> _ => case_fun (pointer_correct gt)
  | |- null_pointer_constant ?e = _ -> _ => case_fun (null_pointer_constant_correct e)
  | |- pointer_to_object ?gt = _ -> _ => case_fun_tac (pointer_to_object_correct gt) autodestruct id_tac
  | |- pointer_to_void ?gt = _ -> _ => case_fun_tac (pointer_to_void_correct gt) autodestruct id_tac
  | |- composite_pointer ?gt1 ?gt2 = _ -> _ => case_fun_tac (composite_pointer_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = Some _ -> _ => intros ?; Tactics.subst_no_fail; Tactics.autoinjections
  | H : AilTypesAux_defns.compatible ?t1 ?t2, Hfind : forall _, ~ AilTypesAux_defns.composite ?t1 ?t2 _ |- _ => destruct (AilTyping_proof.compatible_composite H Hfind)
  | |- _ /\ _ => split
  | |- D.wellAnnotatedExpression' A S G _ _ => 
        econstructor (
          solve [
              eassumption
            | constructor; apply usual_arithmetic_integer_correct
            | econstructor (eassumption)
            | finish fail
            | inversion 1; now my_auto
            | econstructor (now repeat constructor)])
  end;
abstract (
  inversion_clear 4;
  repeat match goal with
  | H : D.wellAnnotatedRValue _ S G ?e' ?gt'
  , Hequiv : D.equivExpression ?e ?e'
  , Hunique : forall _ _ _ _ _, D.equivExpression ?e _ -> _ -> ?gt = _ |- _ => notSame gt gt'; pose proof (Hunique _ _ _ _ _ Hequiv H); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : AilTypesAux_defns.composite ?t1 ?t2 ?t3
  , H2 : AilTypesAux_defns.composite ?t1 ?t2 ?t3' |- _ =>
      notSame t3 t3';
      pose proof (AilTypesAux_proof.composite_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H : D.usualArithmetic _ _ _ |- context[usual_arithmetic_integer] =>
      inversion_clear H;
      repeat apply f_equal;
      eapply usualArithmeticInteger_functional;
      [eapply usual_arithmetic_integer_correct; eassumption | assumption]
  end;
  repeat match goal with
  | H1 : ~ D.nullPointerConstant ?e1
  , H2 : D.nullPointerConstant ?e2
  , Hequiv1 : D.equivExpression ?e ?e1
  , Hequiv2 : D.equivExpression ?e ?e2 |- _ => exfalso; apply H1; exact (nullPointerConstant_equiv (equivExpression_trans (equivExpression_symm Hequiv2) Hequiv1) H2)
  | Hfalse : forall _ _, GenPointer _ ?t   = GenPointer _ _ -> ~ AilTypesAux_defns.object _ , H : AilTypesAux_defns.object ?t |- _ => destruct (Hfalse _ _ eq_refl H)
  | Hfalse : forall _ _, GenPointer _ Void = GenPointer _ _ -> ~ AilTypesAux_defns.void   _ |- _ => exfalso; apply (Hfalse _ _ eq_refl); constructor
  | H  : D.usualArithmetic ?gt1 ?gt2 _ , Hfalse : forall _, ~ D.usualArithmetic ?gt1 ?gt2 _ |- _  => destruct (Hfalse _ H)
  | Hnull : D.nullPointerConstant ?e
  , H : D.wellAnnotatedRValue _ S G ?e (GenPointer _ ?t) |- _ =>
      notSame t Void;
      destruct (nullPointerConstant_wellAnnotatedRValue Hnull H);
      Tactics.subst_no_fail; Tactics.autoinjections
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end; finish fail).
Qed.

Lemma wellAnnotatedExpression'_neg_conditional1 {A2 B1 B2 : Set} {S : sigma B1 B2} {G} {e1 : expression A2} :
  (forall {A1' A2'} {A' : annotation A1' A2'} e1' gt,
     D.equivExpression e1 e1' ->
     ~ D.wellAnnotatedRValue A' S G e1' gt) ->
  forall {A1' A2'} {A' : annotation A1' A2'} e1' e2' e3' gtc,
     D.equivExpression e1 e1' ->    
    ~ D.wellAnnotatedExpression' A' S G (Conditional e1' e2' e3') gtc.
Proof. intros H; inversion_clear 2; eapply H; eassumption. Qed.

Lemma wellAnnotatedExpression'_neg_conditional2 {A2 B1 B2 : Set} {S : sigma B1 B2} {G} {e2 : expression A2} :
  (forall {A1' A2'} {A' : annotation A1' A2'} e2' gt,
     D.equivExpression e2 e2' ->
     ~ D.wellAnnotatedRValue A' S G e2' gt) ->
  forall {A1' A2'} {A' : annotation A1' A2'} e1' e2' e3' gtc,
     D.equivExpression e2 e2' ->    
    ~ D.wellAnnotatedExpression' A' S G (Conditional e1' e2' e3') gtc.
Proof. intros H; inversion_clear 2; eapply H; eassumption. Qed.

Lemma wellAnnotatedExpression'_neg_conditional3 {A2 B1 B2 : Set} {S : sigma B1 B2} {G} {e3 : expression A2} :
  (forall {A1' A2'} {A' : annotation A1' A2'} e3' gt,
     D.equivExpression e3 e3' ->
     ~ D.wellAnnotatedRValue A' S G e3' gt) ->
  forall {A1' A2'} {A' : annotation A1' A2'} e1' e2' e3' gtc,
     D.equivExpression e3 e3' ->    
    ~ D.wellAnnotatedExpression' A' S G (Conditional e1' e2' e3') gtc.
Proof. intros H; inversion_clear 2; eapply H; eassumption. Qed.

Definition annotate_expression'_correct_Constant {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {c} :
  annotate_expression'_spec A S G (Constant c).
Proof.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Constant c)).
  unfold_goal.
  unfold option_bind.
  destruct c; simpl;
  repeat match goal with
  | |- context[type_of_constant ?ic] =>
      notHyp (findSpec (type_of_constant ic) (D.typeOfConstant ic));
      pose proof (type_of_constant_correct ic)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  end;
  repeat match goal with
  | |- D.equivExpression' _ _ => constructor
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => now my_auto
  | |- forall _ _ _ _ _, _ -> _ -> ~ _ => inversion_clear 3
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | H : D.typeOfConstant ?ic ?git |- type_of_constant ?ic = ?git => eapply typeOfConstant_functional; eassumption
  | |- ?c _ = ?c _ => apply f_equal
  end.
Qed.

Lemma annotate_expression'_correct_Unary {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {aop} {e : expression A1} :
  annotate_expression_spec A S G e ->
  annotate_expression'_spec A S G (Unary aop e).
Proof.
  intros Hcorrect.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Unary aop e)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold option_map.
  unfold andb.
  unfold orb.
  destruct aop;
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | H : annotate_expression_spec A S G ?e |- match annotate_expression A S G ?e with _ => _ end = _ -> _ => unfold annotate_expression_spec in H; destruct (annotate_expression A S G e)
  | |- match type_of A ?e with _ => _ end = _ -> _ => destruct (type_of A e)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- promotion ?gt = _ -> _ => case_fun (promotion_correct gt)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- AilTypesAux.real ?t = _ -> _ => case_fun (AilTypesAux_proof.real_correct t)
  | |- AilTypesAux.pointer ?gt = _ -> _ => case_fun (AilTypesAux_proof.pointer_correct gt)
  | |- AilTypesAux.complete ?t = _ -> _ => case_fun (AilTypesAux_proof.complete_correct t)
  | |- AilTypesAux.object ?t = _ -> _ => case_fun (AilTypesAux_proof.object_correct t)
  | |- AilTypesAux.unqualified ?q = _ -> _ => case_fun (AilTypesAux_proof.unqualified_correct q)
  | |- AilTypesAux.modifiable ?q ?t = _ -> _ => case_fun (AilTypesAux_proof.modifiable_correct q t)
  | |- AilTypesAux.lvalue_conversion ?t = _ -> _ => case_fun (AilTypesAux_proof.lvalue_conversion_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedExpression _ S G ?e2 ?gtc2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedExpression _ _ _ _ _ -> ?gtc1 = _ |- _ =>
      notSame gtc1 gtc2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H : D.wellAnnotatedLValue _ _ _ _ _ _ |- _ => inversion_clear H
  | H1 : D.promotion ?t ?t1 
  , H2 : D.promotion ?t ?t2 |- _ => notSame t1 t2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : AilTypesAux_defns.lvalueConversion ?t ?t1 
  , H2 : AilTypesAux_defns.lvalueConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (AilTypesAux_proof.lvalueConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | _ => genType_tac
  end;
  match goal with
  | H2 : D.wellAnnotatedExpression _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | H1 : ~ ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
  | |- _ => reflexivity
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Comma {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Comma e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Comma e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | |- _ => reflexivity
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Mul {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Mul) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Mul) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Div {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Div) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Div) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Mod {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Mod) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Mod) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Add {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Add) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Add) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | |- pointer_to_complete_object ?gt = _ -> _ => case_fun_tac (pointer_to_complete_object_correct gt) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | H : AilTypesAux_defns.complete ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.complete _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Sub {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Sub) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Sub) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | |- pointer_to_complete_object ?gt = _ -> _ => case_fun_tac (pointer_to_complete_object_correct gt) autodestruct id_tac
  | |- pointers_to_compatible_complete_objects ?gt1 ?gt2 = _ -> _ => case_fun_tac (pointers_to_compatible_complete_objects_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | H : AilTypesAux_defns.complete ?t1 , Hfalse : forall _ _, GenPointer ?q1 ?t1 = GenPointer _ _ -> ~ AilTypesAux_defns.complete _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ -> GenPointer ?q2 ?t2 = _ -> ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Shl {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Shl) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Shl) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- promotion ?gt = _ -> _ => case_fun (promotion_correct gt)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.promotion ?gt ?gt1 
  , H2 : D.promotion ?gt ?gt2 |- _ => notSame gt1 gt2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Shr {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Shr) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Shr) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- promotion ?gt = _ -> _ => case_fun (promotion_correct gt)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.promotion ?gt ?gt1 
  , H2 : D.promotion ?gt ?gt2 |- _ => notSame gt1 gt2; pose proof (promotion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Band {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Band) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Band) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Bor {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Bor) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Bor) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Arithmetic_Xor {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 (Arithmetic Xor) e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 (Arithmetic Xor) e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- usual_arithmetic ?gt1 ?gt2 = _ -> _ => case_fun (usual_arithmetic_correct gt1 gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_And {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 And e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 And e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- scalar ?gt = _ -> _ => case_fun (scalar_correct gt)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Or {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Or e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Or e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- scalar ?gt = _ -> _ => case_fun (scalar_correct gt)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Lt {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Lt e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Lt e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- real ?gt = _ -> _ => case_fun (real_correct gt)
  | |- pointers_to_compatible_objects ?gt1 ?gt2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ -> GenPointer ?q2 ?t2 = _ -> ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q ?t = _ -> ~ AilTypesAux_defns.object _
  , H : AilTypesAux_defns.object ?t |- False => now eapply (Hfalse q t eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Gt {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Gt e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Gt e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- real ?gt = _ -> _ => case_fun (real_correct gt)
  | |- pointers_to_compatible_objects ?gt1 ?gt2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ -> GenPointer ?q2 ?t2 = _ -> ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q ?t = _ -> ~ AilTypesAux_defns.object _
  , H : AilTypesAux_defns.object ?t |- False => now eapply (Hfalse q t eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Le {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Le e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Le e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- real ?gt = _ -> _ => case_fun (real_correct gt)
  | |- pointers_to_compatible_objects ?gt1 ?gt2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ -> GenPointer ?q2 ?t2 = _ -> ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q ?t = _ -> ~ AilTypesAux_defns.object _
  , H : AilTypesAux_defns.object ?t |- False => now eapply (Hfalse q t eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Ge {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Ge e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Ge e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- real ?gt = _ -> _ => case_fun (real_correct gt)
  | |- pointers_to_compatible_objects ?gt1 ?gt2 = _ -> _ => case_fun_tac (pointers_to_compatible_objects_correct gt1 gt2) autodestruct id_tac
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | Hfalse : forall _ _ _ _, GenPointer ?q1 ?t1 = _ -> GenPointer ?q2 ?t2 = _ -> ~ AilTypesAux_defns.compatible _ _
  , H : AilTypesAux_defns.compatible ?t1 ?t2 |- False => now eapply (Hfalse q1 q2 t1 t2 eq_refl eq_refl H)
  | Hfalse : forall _ _, GenPointer ?q ?t = _ -> ~ AilTypesAux_defns.object _
  , H : AilTypesAux_defns.object ?t |- False => now eapply (Hfalse q t eq_refl H)
  | _ => progress genType_tac
  | H : _ \/ _ |- _ => destruct H
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Eq {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Eq e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Eq e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | H1 : D.wellAnnotatedRValue _ _ _ ?e1' ?gt1
  , H2 : D.wellAnnotatedRValue _ _ _ ?e2' ?gt2
  , Hequiv1 : D.equivExpression ?e1 ?e1'
  , Hequiv2 : D.equivExpression ?e2 ?e2'
  , Hunique1 : forall _ _ _ _ _, D.equivExpression ?e1 _ -> _ -> ?gt1 = _
  , Hunique2 : forall _ _ _ _ _, D.equivExpression ?e2 _ -> _ -> ?gt2 = _
    |- well_typed_equality ?gt1 ?gt2 (null_pointer_constant ?e1') (null_pointer_constant ?e2') = _ -> _ =>
      case_fun (
        well_typed_equality_correct
          Hequiv1 Hequiv2
          H1 H2
          Hunique1 Hunique2
          (or_introl eq_refl)
      )
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => assumption
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1; reflexivity
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | Hfalse : forall _ _ _ _ _ _, D.equivExpression _ _ -> D.equivExpression _ _ -> ~ D.wellAnnotatedExpression' _ _ _ _ _ |- False =>
      eapply Hfalse; finish eassumption
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => contradiction || now genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Binary_Ne {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Binary e1 Ne e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Binary e1 Ne e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | H1 : D.wellAnnotatedRValue _ _ _ ?e1' ?gt1
  , H2 : D.wellAnnotatedRValue _ _ _ ?e2' ?gt2
  , Hequiv1 : D.equivExpression ?e1 ?e1'
  , Hequiv2 : D.equivExpression ?e2 ?e2'
  , Hunique1 : forall _ _ _ _ _, D.equivExpression ?e1 _ -> _ -> ?gt1 = _
  , Hunique2 : forall _ _ _ _ _, D.equivExpression ?e2 _ -> _ -> ?gt2 = _
    |- well_typed_equality ?gt1 ?gt2 (null_pointer_constant ?e1') (null_pointer_constant ?e2') = _ -> _ =>
      case_fun (
        well_typed_equality_correct
          Hequiv1 Hequiv2
          H1 H2
          Hunique1 Hunique2
          (or_intror eq_refl)
      )
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => assumption
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1; reflexivity
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | Hfalse : forall _ _ _ _ _ _, D.equivExpression _ _ -> D.equivExpression _ _ -> ~ D.wellAnnotatedExpression' _ _ _ _ _ |- False =>
      eapply Hfalse; finish eassumption
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => contradiction || now genType_tac
  end.
Qed.

Lemma annotate_expression'_correct_Assign {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (Assign e1 e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Assign e1 e2)); simpl.
  fold (annotate_rvalue A S G).
  fold (annotate_assignee A S G).
  unfold option_bind.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_expression A S G ?e with _ => _ end = _ -> _ => unfold annotate_expression_spec in H; destruct (annotate_expression A S G e)
  | H : annotate_expression_spec A S G ?e2 |- match annotate_assignee A S G ?t1' ?e2 with _ => _ end = _ -> _ => apply @annotate_assignee_correct_aux with (t1:=t1') in H; unfold annotate_assignee_spec in H; destruct (annotate_assignee A S G t1' e2)
  | |- match type_of A ?e with _ => _ end = _ -> _ => destruct (type_of A e)
  | |- AilTypesAux.modifiable ?q ?t = _ -> _ => case_fun (AilTypesAux_proof.modifiable_correct q t)
  | |- context[AilTypesAux.pointer_conversion ?t] => let H := fresh in notHyp (AilTypesAux_defns.pointerConversion t (AilTypesAux.pointer_conversion t)); pose proof (AilTypesAux_proof.pointer_conversion_correct t) as H; unfold findSpec in H
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedExpression _ S G ?e2 ?gtc2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedExpression _ _ _ _ _ -> ?gtc1 = _ |- _ =>
      notSame gtc1 gtc2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : AilTypesAux_defns.pointerConversion ?t1 ?t2
  , H2 : AilTypesAux_defns.pointerConversion ?t1 ?t2' |- _ =>
      notSame t2 t2';
      pose proof (AilTypesAux_proof.pointerConversion_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H : D.wellAnnotatedLValue _ _ _ _ _ _ |- _ => inversion_clear H
  | _ => genType_tac
  end;
  match goal with
  | H2 : D.wellAnnotatedExpression _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | H2 : D.wellAnnotatedAssignee _ S G ?t1 ?e2'
  , Hequiv : D.equivExpression ?e2 ?e2'
  , H  : forall _ _ _ _, D.equivExpression ?e2 _ -> ~ D.wellAnnotatedAssignee _ S G ?t1 _ |- False =>
      destruct (H _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  end.
Qed.

Lemma annotate_expression'_correct_CompoundAssign {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {aop} {e1 e2 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression'_spec A S G (CompoundAssign e1 aop e2).
Proof.
  intros Hcorrect1 Hcorrect2.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (CompoundAssign e1 aop e2)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold option_bind.
  unfold andb.
  unfold orb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_expression A S G ?e with _ => _ end = _ -> _ => unfold annotate_expression_spec in H; destruct (annotate_expression A S G e)
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- match type_of A ?e with _ => _ end = _ -> _ => destruct (type_of A e)
  | |- AilTypesAux.modifiable ?q ?t = _ -> _ => case_fun (AilTypesAux_proof.modifiable_correct q t)
  | |- AilTypesAux.lvalue_conversion ?t = _ -> _ => case_fun (AilTypesAux_proof.lvalue_conversion_correct t)
  | |- AilTypesAux.arithmetic ?t = _ -> _ => case_fun (AilTypesAux_proof.arithmetic_correct t)
  | |- AilTypesAux.pointer_to_complete_object ?gt = _ -> _ => case_fun_tac (AilTypesAux_proof.pointer_to_complete_object_correct gt) autodestruct id_tac
  | |- integer ?gt = _ -> _ => case_fun (integer_correct gt)
  | |- arithmetic ?gt = _ -> _ => case_fun (arithmetic_correct gt)
  | |- well_typed_binary_arithmetic ?gt1 ?aop ?gt2 = _ -> _ => case_fun (well_typed_binary_arithmetic_correct gt1 aop gt2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (finish eassumption)
  end;
  abstract (
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H2 : D.wellAnnotatedExpression _ S G ?e2 ?gtc2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedExpression _ _ _ _ _ -> ?gtc1 = _ |- _ =>
      notSame gtc1 gtc2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : D.usualArithmetic ?gt1 ?gt2 ?gt, H2 : D.usualArithmetic ?gt1 ?gt2 ?gt' |- _ =>
      notSame gt gt';
      pose proof (usualArithmetic_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H1 : AilTypesAux_defns.lvalueConversion ?t ?t1 
  , H2 : AilTypesAux_defns.lvalueConversion ?t ?t2 |- _ => notSame t1 t2; pose proof (AilTypesAux_proof.lvalueConversion_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections
  | H : ?c = Add \/ ?c = Sub |- _ => notSame c Add; notSame c Sub; destruct H; congruence
  | H : ~ (Add = Add \/ _) |- _ => exfalso; apply H; left ; reflexivity
  | H : ~ (_ \/ Sub = Sub) |- _ => exfalso; apply H; right; reflexivity
  | H : D.wellAnnotatedLValue _ _ _ _ _ _ |- _ => inversion_clear H
  | H : ~ _ \/ _ |- _ => destruct H
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | H2 : D.wellAnnotatedExpression _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | H : AilTypesAux_defns.complete ?t1 , Hfalse : forall _ _, Pointer ?q1 ?t1 = Pointer _ _ -> ~ AilTypesAux_defns.complete _ |- False => now eapply (Hfalse q1 t1 eq_refl H)
  | _ => progress genType_tac
  end).
Qed.

Lemma annotate_expression'_correct_Conditional {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e1 e2 e3 : expression A1} :
  annotate_expression_spec A S G e1 ->
  annotate_expression_spec A S G e2 ->
  annotate_expression_spec A S G e3 ->
  annotate_expression'_spec A S G (Conditional e1 e2 e3).
Proof.
  intros Hcorrect1 Hcorrect2 Hcorrect3.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Conditional e1 e2 e3)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | H1 : D.wellAnnotatedRValue _ _ _ ?e1' ?gt1
  , H2 : D.wellAnnotatedRValue _ _ _ ?e2' ?gt2
  , H3 : D.wellAnnotatedRValue _ _ _ ?e3' ?gt3
  , Hequiv1 : D.equivExpression ?e1 ?e1'
  , Hequiv2 : D.equivExpression ?e2 ?e2'
  , Hequiv3 : D.equivExpression ?e3 ?e3'
  , Hunique1 : forall _ _ _ _ _, D.equivExpression ?e1 _ -> _ -> ?gt1 = _
  , Hunique2 : forall _ _ _ _ _, D.equivExpression ?e2 _ -> _ -> ?gt2 = _
  , Hunique3 : forall _ _ _ _ _, D.equivExpression ?e3 _ -> _ -> ?gt3 = _
    |- well_typed_conditional ?gt1 ?gt2 ?gt3 (null_pointer_constant ?e2') (null_pointer_constant ?e3') = _ -> _ =>
      case_fun (
        well_typed_conditional_correct_aux
          Hequiv1 Hequiv2 Hequiv3
          H1 H2 H3
          Hunique1 Hunique2 Hunique3
      )
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end;
  match goal with
  | |- D.equivExpression' _ _ =>
    constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ =>
    assumption
  | H : forall _ _ _ _ _ _ _, _ -> _ -> _ -> _ -> ?gtc = _|- forall _ _ _ _ _, _ -> _ -> ?gtc = _ =>
      inversion_clear 1; apply H; assumption
  | H : forall _ _ _ _ _ _ _, _ -> _ -> _ -> ~ _ |- forall _ _ _ _ _, _ -> ~ _ =>
      inversion_clear 1; apply H; finish eassumption
  | |- forall _ _ _ _ _, _ -> ~ _ =>
      inversion_clear 1;
      solve [
        eapply wellAnnotatedExpression'_neg_conditional1; eassumption
      | eapply wellAnnotatedExpression'_neg_conditional2; eassumption
      | eapply wellAnnotatedExpression'_neg_conditional3; eassumption
      ]
  end.
Qed.

Lemma annotate_expression'_correct_Cast {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e : expression A1} {q} {t}:
  annotate_expression_spec A S G e ->
  annotate_expression'_spec A S G (Cast q t e).
Proof.
  intros Hcorrect.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Cast q t e)); simpl.
  fold (annotate_rvalue A S G).
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- scalar ?gt = _ -> _ => case_fun (scalar_correct gt)
  | |- AilTypesAux.scalar ?t = _ -> _ => case_fun (AilTypesAux_proof.scalar_correct t)
  | |- AilWf.wf_lvalue ?q ?t = _ -> _ => case_fun (AilWf_proof.wf_lvalue_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | Hfalse : forall _, ~ ?P _, H : ?P _ |- False => exact (Hfalse _ H)
  | _ => contradiction || (progress genType_tac)
  end.
Qed.

Lemma annotate_expression'_correct_Call {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e : expression A1} {es : list (expression A1)}:
  annotate_expression_spec A S G e ->
  annotate_arguments_spec A S G es ->
  annotate_expression'_spec A S G (Call e es).
Proof.
  intros Hcorrect Harguments_correct.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Call e es)); simpl.
  fold (annotate_rvalue A S G).
  fold (annotate_assignee A S G).
  fold (annotate_arguments A S G).
  unfold option_bind.
  repeat match goal with
  | H : annotate_expression_spec A S G ?e |- match annotate_rvalue A S G ?e with _ => _ end = _ -> _ => apply annotate_rvalue_correct_aux in H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | H : annotate_arguments_spec A S G ?es |- match annotate_arguments A S G ?es ?ps with _ => _ end = _ -> _ => pose proof (H ps); destruct (annotate_arguments A S G es ps)
  | |- AilTypesAux.unqualified ?q = _ -> _ => case_fun (AilTypesAux_proof.unqualified_correct q)
  | |- AilTypesAux.scalar ?t = _ -> _ => case_fun (AilTypesAux_proof.scalar_correct t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => autodestruct H
  | |- D.equivExpression' _ _ =>  constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (solve [eassumption | econstructor; eassumption])
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 ?gt2
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> D.wellAnnotatedRValue _ _ _ _ _ -> ?gt1 = _ |- _ =>
      notSame gt1 gt2;
      pose proof (H _ _ _ _ _ Hequiv H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  end;
  match goal with
  | H2 : D.wellAnnotatedRValue _ S G ?e2 _
  , Hequiv : D.equivExpression ?e1 ?e2
  , H  : forall _ _ _ _ _, D.equivExpression ?e1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ _ Hequiv H2)
  | H2 : D.wellAnnotatedArguments _ S G ?es2 _
  , Hequiv : D.equivArguments ?es1 ?es2
  , H  : forall _ _ _ _, D.equivArguments ?es1 _ -> ~ _ |- False =>
      destruct (H _ _ _ _ Hequiv H2)
  | _ => congruence
  end.
Qed.

Lemma annotate_expression'_correct_Var {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {v}:
  D.disjoint G S ->
  annotate_expression'_spec A S G (Var v).
Proof.
  intros Hdisjoint.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (Var v)).
  unfold annotate_expression'.
  repeat match goal with
  | |- lookup ?C v = _ -> _ => case_fun (lookup_correct C v)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- D.equivExpression' _ _ => constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (finish eassumption)
  | |- _ /\ _ => split
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H1 : D.lookup ?C ?v ?r1
  , H2 : D.lookup ?C ?v ?r2 |- _ => notSame r1 r2; pose proof (lookup_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | HG : D.lookup G ?v _
  , HS : D.lookup S ?v _ |- _ => exfalso; eapply Hdisjoint; eexists; eassumption
  | H1 : ~ ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => reflexivity
  end.
Qed.

Lemma annotate_expression'_correct_SizeOf {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {q} {t}:
  annotate_expression'_spec A S G (SizeOf q t).
Proof.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (SizeOf q t)).
  unfold annotate_expression'.
  unfold negb.
  unfold andb.
  repeat match goal with
  | |- AilTypesAux.function ?t = _ -> _ => case_fun (AilTypesAux_proof.function_correct t)
  | |- AilTypesAux.incomplete ?t = _ -> _ => case_fun (AilTypesAux_proof.incomplete_correct t)
  | |- AilWf.wf_lvalue ?q ?t = _ -> _ => case_fun (AilWf_proof.wf_lvalue_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- D.equivExpression' _ _ => constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (finish eassumption)
  | |- _ /\ _ => split
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  match goal with
  | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => contradiction || congruence
  end.
Qed.

Lemma annotate_expression'_correct_AlignOf {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {q} {t}:
  annotate_expression'_spec A S G (AlignOf q t).
Proof.
  unfold annotate_expression'_spec.
  pull_out (option (expression' A2 * genTypeCategory)) (annotate_expression' A S G (AlignOf q t)).
  unfold annotate_expression'.
  unfold negb.
  unfold andb.
  repeat match goal with
  | |- AilTypesAux.function ?t = _ -> _ => case_fun (AilTypesAux_proof.function_correct t)
  | |- AilTypesAux.incomplete ?t = _ -> _ => case_fun (AilTypesAux_proof.incomplete_correct t)
  | |- AilWf.wf_lvalue ?q ?t = _ -> _ => case_fun (AilWf_proof.wf_lvalue_correct q t)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- D.equivExpression' _ _ => constructor; assumption
  | |- D.wellAnnotatedExpression' _ _ _ _ _ => econstructor (finish eassumption)
  | |- _ /\ _ => split
  end;
  match goal with
  | |- forall _ _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  match goal with
  | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => contradiction || congruence
  end.
Qed.

Definition annotate_arguments_correct_nil {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} :
  annotate_arguments_spec A S G nil.
Proof. destruct ps; my_auto; inversion_clear 1; inversion_clear 1. Qed.

Lemma annotate_arguments_correct_cons {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e : expression A1} {es : list (expression A1)}:
  annotate_expression_spec A S G e ->
  annotate_arguments_spec A S G es ->
  annotate_arguments_spec A S G (e :: es).
Proof.
  intros Hcorrect Hcorrect_arguments ps.
  pull_out (option (list (expression A2))) (annotate_arguments A S G (e :: es) ps); simpl.
  unfold option_bind.
  repeat match goal with
  | H : annotate_arguments_spec A S G ?es |- match annotate_arguments A S G ?es ?ps with _ => _ end = _ -> _ => pose proof (H ps); destruct (annotate_arguments A S G es ps)
  | |- context[AilTypesAux.pointer_conversion ?t] => let H := fresh in notHyp (AilTypesAux_defns.pointerConversion t (AilTypesAux.pointer_conversion t)); pose proof (AilTypesAux_proof.pointer_conversion_correct t) as H; unfold findSpec in H  
  | H : annotate_expression_spec A S G ?e2 |- match annotate_assignee A S G ?t1' ?e2 with _ => _ end = _ -> _ => apply @annotate_assignee_correct_aux with (t1:=t1') in H; unfold annotate_assignee_spec in H; destruct (annotate_assignee A S G t1' e2)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- D.equivArguments _ _ => constructor; assumption
  | |- D.wellAnnotatedArguments _ _ _ _ _ => econstructor (finish eassumption)
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => destruct H
  end;
  match goal with
  | |- forall _ _ _ _, _ -> _ -> _ = _ => do 2 inversion_clear 1
  | |- forall _ _ _ _, _ -> ~ _ => do 2 inversion_clear 1
  end;
  repeat match goal with
  | H : D.wellAnnotatedArguments _ S G ?es2 ?ps
  , Hequiv : D.equivArguments ?es1 ?es2
  , Hunique : forall _ _ _ _, D.equivArguments ?es1 _ -> ~ D.wellAnnotatedArguments _ S G _ ?ps |- _ =>
      destruct (Hunique _ _ _ _ Hequiv H)
  | H1 : AilTypesAux_defns.pointerConversion ?t1 ?t2
  , H2 : AilTypesAux_defns.pointerConversion ?t1 ?t2' |- _ =>
      notSame t2 t2';
      pose proof (AilTypesAux_proof.pointerConversion_functional H1 H2);
      Tactics.subst_no_fail; Tactics.autoinjections
  | H2 : D.wellAnnotatedAssignee _ S G ?t1 ?e2'
  , Hequiv : D.equivExpression ?e2 ?e2'
  , H  : forall _ _ _ _, D.equivExpression ?e2 _ -> ~ D.wellAnnotatedAssignee _ S G ?t1 _ |- False =>
      destruct (H _ _ _ _ Hequiv H2)
  end.
Qed.

Lemma annotate_expression_correct_AnnotatedExpression {A1 A2 B1 B2} {A : annotation A1 A2} {S : sigma B1 B2} {G} {a} {e : expression' A1} :
  annotate_expression'_spec A S G e ->
  annotate_expression_spec A S G (AnnotatedExpression a e).
Proof.
  intros Hcorrect.
  unfold annotate_expression_spec.
  pull_out (option (expression A2)) (annotate_expression A S G (AnnotatedExpression a e)); simpl.
  unfold option_bind.
  repeat match goal with
  | H : annotate_expression'_spec A S G ?es |- match annotate_expression' A S G ?e with _ => _ end = _ -> _ => unfold annotate_expression'_spec in H; destruct (annotate_expression' A S G e)
  | _ => context_destruct
  | |- Some _ = ?v -> _ => is_var v; intros ?; subst
  | |- None   = ?v -> _ => is_var v; intros ?; subst
  | |- D.equivExpression _ _ => constructor; assumption
  | |- D.wellAnnotatedExpression _ _ _ _ _ =>   constructor; [reflexivity | unfold type_of; rewrite id_add_get; assumption]
  | |- _ /\ _ => split
  | H : _ /\ _ |- _ => destruct H
  end;
  inversion_clear 1;
  inversion_clear 1;
  match goal with
  | Hunique : forall _ _ _ _ _, D.equivExpression' ?e _ -> _ -> _ = _
  , Hequiv : D.equivExpression' ?e _ |- _ = _ => unfold type_of; rewrite id_add_get; (eapply Hunique; [eapply Hequiv|]; eassumption)
  | Hfalse : forall _ _ _ _ _, D.equivExpression' ?e _ -> ~ _
  , Hequiv : D.equivExpression' ?e _ |- False => eapply Hfalse; [eapply Hequiv|]; eassumption
  end.
Qed.

Definition annotate_expression_correct {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1 A2 : Set} (A: annotation A1 A2) (e : expression A1), annotate_expression_spec A S G e.
Proof.
  intros Hdisjoint ? ? A.
  eapply (expression_nrect (fun e => annotate_expression'_spec A S G e)
                           (fun e => annotate_expression_spec  A S G e)
                           (fun es => annotate_arguments_spec A S G es));
  intros.
  apply annotate_expression'_correct_Unary; assumption.
  destruct bop.
  destruct aop.
  apply annotate_expression'_correct_Binary_Arithmetic_Mul; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Div; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Mod; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Add; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Sub; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Shl; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Shr; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Band; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Bor; assumption.
  apply annotate_expression'_correct_Binary_Arithmetic_Xor; assumption.
  apply annotate_expression'_correct_Binary_Comma; assumption.
  apply annotate_expression'_correct_Binary_And; assumption.
  apply annotate_expression'_correct_Binary_Or; assumption.
  apply annotate_expression'_correct_Binary_Lt; assumption.
  apply annotate_expression'_correct_Binary_Gt; assumption.
  apply annotate_expression'_correct_Binary_Le; assumption.
  apply annotate_expression'_correct_Binary_Ge; assumption.
  apply annotate_expression'_correct_Binary_Eq; assumption.
  apply annotate_expression'_correct_Binary_Ne; assumption.
  apply annotate_expression'_correct_Assign; assumption.
  apply annotate_expression'_correct_CompoundAssign; assumption.
  apply annotate_expression'_correct_Conditional; assumption.
  apply annotate_expression'_correct_Cast; assumption.
  apply annotate_expression'_correct_Call; assumption.
  apply annotate_expression'_correct_Constant; assumption.
  apply annotate_expression'_correct_Var; assumption.
  apply annotate_expression'_correct_SizeOf; assumption.
  apply annotate_expression'_correct_AlignOf; assumption.
  apply annotate_arguments_correct_nil; assumption.
  apply annotate_arguments_correct_cons; assumption.
  apply annotate_expression_correct_AnnotatedExpression; assumption.
Qed.

Lemma annotate_rvalue_correct {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1 A2 : Set} (A: annotation A1 A2) (e : expression A1), annotate_rvalue_spec A S G e.
Proof.
  intros Hdisjoint ? ? A e.
  exact (annotate_rvalue_correct_aux (annotate_expression_correct Hdisjoint A e)).  
Qed.

Lemma annotate_assignee_correct {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1 A2 : Set} (A: annotation A1 A2) t1 (e2 : expression A1), annotate_assignee_spec A S G t1 e2.
Proof.
  intros Hdisjoint ? ? A t1 e2.
  exact (annotate_assignee_correct_aux (annotate_expression_correct Hdisjoint A e2)).  
Qed.

Lemma annotate_definition_correct {B1 B2 : Set} {S : sigma B1 B2} {G}  :
  D.disjoint G S ->
  forall {A1 A2 : Set} (A : annotation A1 A2) (d1 : _ * expression A1),
    match annotate_definition A S G d1 with
    | Some d2 =>
        D.equivDefinition d1 d2 /\
        D.wellAnnotatedDefinition A S G d2
    | None          =>
        forall {A1' A2' : Set} (A' : annotation A1' A2') d2,
          D.equivDefinition d1 d2 ->
          ~ D.wellAnnotatedDefinition A' S G d2
    end.
Proof.
  intros Hdisjoint ? ? A d1.
  unfold annotate_definition.
  unfold option_bind.
  repeat match goal with
  | |- lookup G ?v = _ -> _ => case_fun (lookup_correct G v)
  | |- annotate_assignee A S G ?t1 ?e2 = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (annotate_assignee_correct Hdisjoint A t1 e2) as H; unfold annotate_assignee_spec in H; destruct (annotate_assignee A S G t1 e2)
  | _ => context_destruct
  end;
  match goal with
  | |- _ /\ _ =>
      intuition; econstructor; finish eassumption
  | |- _ =>
      inversion_clear 1;
      inversion_clear 1;
      repeat match goal with
      | H1 : D.lookup ?C ?v ?r1
      , H2 : D.lookup ?C ?v ?r2 |- _ => notSame r1 r2; pose proof (lookup_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
      end;
      match goal with
      | H : forall _ _ _ _, _ -> ~ _ |- False => eapply H; eassumption
      | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
      | _ => contradiction
      end
  end.
Qed.

Lemma annotate_definitions_correct {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1 A2 : Set} (A : annotation A1 A2) (ds1 : list (_ * expression A1)),
    match annotate_definitions A S G ds1 with
    | Some ds2 =>
        D.equivDeclaration ds1 ds2 /\
        allList (D.wellAnnotatedDefinition A S G) ds2
    | None          =>
      forall {A1' A2' : Set} (A' : annotation A1' A2') ds2,
        D.equivDeclaration ds1 ds2 ->
        ~ allList (D.wellAnnotatedDefinition A' S G) ds2
    end.
Proof.
  intros Hdisjoint ? ? A ds1.
  induction ds1; simpl;
  repeat match goal with
  | |- context[annotate_definition A S G ?d] =>
      pose proof (annotate_definition_correct Hdisjoint A d);
      destruct (annotate_definition A S G d);
      simpl
  | |- context[annotate_definitions A S G ?ds] =>
      destruct (annotate_definitions A S G ds);
      simpl
  | H : _ * _ |- _ => destruct H
  end;
  match goal with
  | |- _ /\ _ =>
      intuition; simpl in *; now my_auto
  | H : forall _ _ _ _, _ -> ~ allList _ _ |- forall _, _ =>
      inversion_clear 1;
      inversion_clear 1;
      eapply H; eassumption
  | H : forall _ _ _ _, _ -> ~ D.wellAnnotatedDefinition _ _ _ _ |- forall _, _ =>
      inversion_clear 1;
      inversion_clear 1;
      eapply H; eassumption
  end.
Qed.

Definition annotate_statement_spec {B1 B2 : Set} {S : sigma B1 B2} {G} (Hdisjoint : D.disjoint G S) {B A1 A2 : Set} (A : annotation A1 A2) t_return (s1 : statement B A1) :=
  match annotate_statement A S G t_return s1 with
  | Some s2 =>
      D.equivStatement s1 s2 /\
      D.wellAnnotatedStatement A S G t_return s2
  | None    =>
      forall {A1' A2' B' : Set} (A' : annotation A1' A2') (s2 : statement B' A2'),
        D.equivStatement s1 s2 ->
        ~ D.wellAnnotatedStatement A' S G t_return s2
  end.

Definition annotate_statement'_spec {B1 B2 : Set} {S : sigma B1 B2} {G} (Hdisjoint : D.disjoint G S) {B A1 A2 : Set} (A : annotation A1 A2) t_return (s1 : statement' B A1) :=
  match annotate_statement' A S G t_return s1 with
  | Some s2 =>
      D.equivStatement' s1 s2 /\
      D.wellAnnotatedStatement' A S G t_return s2
  | None    =>
    forall {A1' A2' B' : Set} (A' : annotation A1' A2') (s2 : statement' B' A2'),
      D.equivStatement' s1 s2 ->
      ~ D.wellAnnotatedStatement' A' S G t_return s2
  end.

Definition annotate_block_spec {B1 B2 : Set} {S : sigma B1 B2} {G} (Hdisjoint : D.disjoint G S) {B A1 A2 : Set} (A : annotation A1 A2) t_return (ss1 : list (statement B A1)) :=
  match annotate_block A S G t_return ss1 with
  | Some ss2 =>
      D.equivBlock ss1 ss2 /\
      allList (D.wellAnnotatedStatement A S G t_return) ss2
  | None     =>
    forall {A1' A2' B' : Set} (A' : annotation A1' A2') (ss2 : list (statement B' A2')),
      D.equivBlock ss1 ss2 ->
      ~ allList (D.wellAnnotatedStatement A' S G t_return) ss2
  end.

Lemma wellFormedBindings_disjointBindings {b} :
  AilTyping_defns.wellFormedBindings b ->
  D.disjointBindings b.
Proof. my_auto. Qed.

Lemma annotate_statement_correct {B1 B2 : Set} {S : sigma B1 B2} {G} (Hdisjoint : D.disjoint G S) {B A1 A2 : Set} (A : annotation A1 A2) t_return (s1 : statement B A1) :
  annotate_statement_spec Hdisjoint A t_return s1.
Proof.
  revert G Hdisjoint.
  apply (
    statement_nrect
      (fun s  => forall G (Hdisjoint : D.disjoint G S), annotate_statement'_spec Hdisjoint A t_return s )
      (fun s  => forall G (Hdisjoint : D.disjoint G S), annotate_statement_spec  Hdisjoint A t_return s )
      (fun ss => forall G (Hdisjoint : D.disjoint G S), annotate_block_spec      Hdisjoint A t_return ss)
  ); intros; unfold_goal; simpl;
  repeat match goal with
  | |- context[annotate_block_aux A (annotate_statement A S ?G t_return) ?ss] => fold (annotate_block A S G t_return ss)
  end;
  unfold option_bind;
  unfold andb;
  repeat match goal with
  | |- fresh_bindings ?bs ?C = _ -> _ => case_fun (fresh_bindings_correct C bs)
  | |- annotate_assignee _ _ ?G ?t1 ?e2 = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (annotate_assignee_correct Hdisjoint A t1 e2) as H; unfold annotate_assignee_spec in H; destruct (annotate_assignee A S G t1 e2)
  | |- annotate_rvalue _ _ ?G ?e = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (annotate_rvalue_correct Hdisjoint A e) as H; unfold annotate_rvalue_spec in H; destruct (annotate_rvalue A S G e)
  | |- annotate_expression _ _ ?G ?e = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (annotate_expression_correct Hdisjoint A e) as H; unfold annotate_expression_spec in H; destruct (annotate_expression A S G e)
  | |- annotate_definitions _ _ ?G ?ds = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (annotate_definitions_correct Hdisjoint A ds) as H; destruct (annotate_definitions A S G ds)
  | IH : forall _ _, annotate_statement_spec _ _ _ ?s |- annotate_statement _ _ ?G _ ?s = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (IH G Hdisjoint) as H; unfold annotate_statement_spec in H; destruct (annotate_statement A S G t_return s)
  | IH : forall _ _, annotate_statement'_spec _ _ _ ?s |- annotate_statement' _ _ ?G _ ?s = ?o -> _ => is_var o; intros ?; subst o; let H := fresh in pose proof (IH G Hdisjoint) as H; unfold annotate_statement'_spec in H; destruct (annotate_statement' A S G t_return s)
  | IH : forall _ _, annotate_block_spec _ _ _ ?ss |- annotate_block _ _ ?G _ ?ss = ?o -> _ =>
      is_var o; intros ?; subst o;
      let Hdisjoint' := fresh in
      (assert (D.disjoint G S) as Hdisjoint'
        by (apply disjoint_freshBindings; [apply wellFormedBindings_disjointBindings|..]; assumption))
      || rename Hdisjoint into Hdisjoint';
      let H := fresh in
      pose proof (IH G Hdisjoint') as H;
      unfold annotate_block_spec in H;
      destruct (annotate_block A S G t_return ss)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (AilTypes_proof.eq_ctype_correct x y)
  | |- AilTyping.well_formed_bindings ?bs = _ -> _ => case_fun (AilTyping_proof.well_formed_bindings_correct bs)
  | H : AilTyping_defns.wellFormedBindings _, IH : forall _ _, boolSpec _ (allList (D.wellTypedStatement _ _ _ _) ?ss) |- annotate_block _ _ ?G _ ?ss = _ -> _ =>
      not_var G;
      let IH' := fresh in
      assert (boolSpec (well_typed_block P S G t_return ss) (allList (D.wellTypedStatement P S G t_return) ss))
        as IH'
        by (apply IH; apply disjoint_freshBindings; [inversion_clear H|..]; assumption);
      case_fun IH'
  | _ => context_destruct
  | _ : ?t = Void |- _ => subst t
  | |- D.wellAnnotatedStatement' _ _ _ _ _ => econstructor (solve [finish eassumption|eapply type_of_constant_correct])
  | |- D.wellAnnotatedStatement  _ _ _ _ _ => econstructor; eassumption
  | |- allList _ _ => now my_auto
  | |- D.equivStatement' _ _ => econstructor; eassumption
  | |- D.equivStatement  _ _ => econstructor; eassumption
  | |- D.equivBlock      _ _ => econstructor; eassumption
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end;
  inversion_clear 1;
  inversion 1; subst;
  repeat match goal with
  | Hunique : forall _ _ _ _ _, D.equivExpression ?e _ -> _ -> ?gt = _ 
  , H : D.wellAnnotatedRValue _ S ?G ?e' ?gt'
  , Hequiv : D.equivExpression ?e ?e' |- _ => notSame gt gt'; pose proof (Hunique _ _ _ _ _ Hequiv H); Tactics.subst_no_fail; Tactics.autoinjections
  | H : D.wellAnnotated _ _ _ _ |- _ => inversion_clear H
  end;
  match goal with
  | H : forall _ _ _ _ _, _ -> ~ _ |- False => eapply H; eassumption
  | H : forall _ _ _ _, _ -> ~ _ |- False => eapply H; eassumption
  | H1 : forall _, ~ ?P _, H2 : ?P _ |- False => destruct (H1 _ H2)
  | _ => finish contradiction
  end.
Qed.

Definition annotate_function_spec {A1 A2 B B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) (p1 : _ * _ * statement B A1) :=
  match annotate_function A S p1 with
  | Some p2 =>
      D.equivFunction p1 p2 /\
      D.wellAnnotatedFunction A S p2
  | None    =>
      forall {A1' A2' B' : Set} (A' : annotation A1' A2') (p2 : _ * _ * statement B' A2'),
        D.equivFunction p1 p2 ->
        ~ D.wellAnnotatedFunction A' S p2
  end.

Lemma annotate_function_correct {A1 A2 B B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) (p1 : _ * _ * statement B A1) :
  annotate_function_spec A S p1.
Proof.
  do 2 unfold_goal.
  unfold option_bind.
  unfold andb.
  repeat match goal with
  | |- fresh_bindings ?bs ?S = _ -> _ => case_fun (fresh_bindings_correct S bs)
  | |- AilTyping.well_formed_bindings ?bs = _ -> _ => case_fun (AilTyping_proof.well_formed_bindings_correct bs)
  | |- AilWf.wf_type ?t = _ -> _ => case_fun (AilWf_proof.wf_type_correct t)
  | H : AilTyping_defns.wellFormedBindings ?bs |- annotate_statement _ _ (Context.add_bindings ?bs Context.empty) ?t ?s = ?o -> _ =>
      notHyp (D.disjoint (Context.add_bindings bs Context.empty) S);
      is_var o; intros ?; subst o;
      let Hdisjoint := fresh in
      let H := fresh in
      assert (D.disjoint (Context.add_bindings bs Context.empty) S) as Hdisjoint
        by (
          apply disjoint_freshBindings; [
            eapply wellFormedBindings_disjointBindings; eassumption
          | assumption
          | let Hfalse := fresh in intros ? [? Hfalse]; inversion Hfalse
          ]
        );
      pose proof (annotate_statement_correct Hdisjoint A t s) as H;
      unfold annotate_statement_spec in H;
      destruct (annotate_statement A S (Context.add_bindings bs Context.empty) t s)
  | _ => context_destruct
  | |- _ /\ _ => intuition; now finish fail
  | |- ~ _ => now (inversion 1; my_auto)
  | |- forall _, _ =>
      intros ? ? ? ? [[] ?] [? ?];
      Tactics.subst_no_fail; Tactics.autoinjections;
      inversion_clear 1;
      contradiction ||
      match goal with
      | Hfalse : forall _ _ _ _ _, _ -> ~ _ |- False => eapply Hfalse; eassumption
      end
  end.
Qed.

Definition annotate_sigma_spec {A1 A2 B : Set} (A : annotation A1 A2) (S1 : sigma B A1) :=
  match annotate_sigma A S1 with
  | Some S2 =>
      D.equivSigma S1 S2 /\
      D.wellAnnotatedSigma A S2
  | None    =>
      forall {A2' : Set} (A' : annotation A1 A2') (S2 : sigma B A2'),
        D.equivSigma S1 S2 ->
        ~ D.wellAnnotatedSigma A' S2
  end.

Lemma annotate_function_map_correct {A1 A2 B B1 B2 : Set} (A : annotation A1 A2) (S : sigma B1 B2) (v : identifier) (p1 : _ * _ * statement B A1) :
  match annotate_function A S p1 with 
  | Some p2 => (fun _ _ => True) v p1 /\ (D.equivFunction p1 p2 /\ D.wellAnnotatedFunction A S p2)
  | None    => ~ (fun _ _ => True) v p1 \/ (fun _ _ => True) v p1 /\ forall p2 : _ * _ * statement B A2, ~ (D.equivFunction p1 p2 /\ D.wellAnnotatedFunction A S p2)
  end.
Proof.
  generalize (annotate_function_correct A S p1); unfold_goal; intros Hcorrect.
  destruct (annotate_function A S p1); simpl.
  - intuition.
  - right; split; trivial; intros p2 [? ?]; eapply Hcorrect; eassumption.
Qed.

Lemma annotate_sigma_correct_aux {A1 A2 B : Set} (A : annotation A1 A2) (S1 : sigma B A1) :
  optionSpec
    (annotate_sigma A S1)
    (fun S2 => D.equivSigma S1 S2 /\ D.wellAnnotatedSigma A S2).
Proof.
  do 2 unfold_goal.
  pose proof (mapP_correct _ eq_identifier_correct (annotate_function_map_correct (B:=B) A S1) S1) as Hcorrect.
  destruct (Context.mapP eq_identifier (fun _ => annotate_function A S1) S1) as [S2|].
  destruct Hcorrect as [_ Hcorrect].

  assert (D.equivSigma S1 S2) as Hequiv.
  constructor.

  intros v p1 Hlookup1.
  destruct (proj1 Hcorrect v p1 Hlookup1) as [p2 [Hlookup2 [Hequiv _]]].
  exists p2; split; assumption.
  
  intros v p1 Hlookup1.
  destruct (proj2 Hcorrect v p1 Hlookup1) as [p2 [Hlookup2 [Hequiv _]]].
  exists p2; split; assumption.

  split.
  assumption.

  intros v p2 Hlookup2.
  destruct (proj2 Hcorrect v p2 Hlookup2) as [p1 [Hlookup1 [Hequiv1 Hannot1]]].
  destruct (proj1 Hcorrect v p1 Hlookup1) as [p2' [Hlookup2' [Hequiv2' Hannot2']]].
  destruct p1  as [[? ?] ?].
  destruct p2  as [[? ?] ?].
  destruct p2' as [[? ?] ?].
  destruct Hequiv1  as [? [? ?]].
  destruct Hequiv2' as [? [? ?]].
  Tactics.subst_no_fail; Tactics.autoinjections.
  apply (wellAnnotatedFunction_equivSigma Hequiv); assumption.

  intros S2 [Hequiv Hannot].
  destruct Hcorrect as [v [p1 [Hlookup1 [Hfalse|[_ Hfalse]]]]]; [apply Hfalse; constructor|].
  destruct (proj1 Hequiv v p1 Hlookup1) as [p2 [Hlookup2 ?]].
  eapply (Hfalse p2).
  split.

  assumption.

  eapply wellAnnotatedFunction_equivSigma.
  eapply equivSigma_symm; eassumption.
  exact (Hannot v p2 Hlookup2).
Qed.

Lemma annotate_sigma_correct {A1 A2 B : Set} (A : annotation A1 A2) (S1 : sigma B A1) :
  annotate_sigma_spec A S1.
Proof.
  unfold_goal.
  pose proof (annotate_sigma_correct_aux A S1) as Hcorrect.
  destruct (annotate_sigma A S1).
  assumption.

  intros ? ? S2' Hequiv Hannot.
  destruct (wellAnnotationSigma_transport A' A Hequiv) as [S2 []].
  eapply Hcorrect.
  split.
  eassumption.
  eapply wellAnnotatedSigma_equivAnnotation; eassumption.
Qed.

Definition annotate_program_spec {A1 A2 B : Set} (A : annotation A1 A2) (p1 : program B A1) :=
  match annotate_program A p1 with
  | Some p2 =>
      D.equivProgram p1 p2 /\
      D.wellAnnotatedProgram A p2
  | None    =>
      forall {A2' : Set} (A' : annotation A1 A2') (p2 : program B A2'),
        D.equivProgram p1 p2 ->
        ~ D.wellAnnotatedProgram A' p2
  end.

Lemma annotate_program_correct {A1 A2 B : Set} (A : annotation A1 A2) (p1 : program B A1) :
  annotate_program_spec A p1.
Proof.
  do 2 unfold_goal.
  unfold option_bind.
  repeat match goal with
  | |- lookup ?S ?v = _ -> _ =>  case_fun (lookup_correct S v)
  | |- annotate_sigma A ?S = ?o -> _ => intros ?; subst; pose proof (annotate_sigma_correct A S) as Hcorrect; unfold annotate_sigma_spec in Hcorrect; destruct (annotate_sigma A S)
  | _ => context_destruct
  end;
  try match goal with
  | |- forall _ _ _, _ -> _ =>
      intros ? ? [];
      inversion_clear 1;
      inversion_clear 1;
      simpl in *; Tactics.subst_no_fail; Tactics.autoinjections;
      match goal with
      | HequivSigma : D.equivSigma ?S1 ?S2
      , Hlookup1 : D.lookup ?S1 ?v ?p1
      , Hlookup2 : D.lookup ?S2 ?v ?p2 |- False =>
          (unify p1 p2; fail 1) ||
          destruct (proj1 HequivSigma _ _ Hlookup1) as [? [Hlookup2' []]];
          pose proof (lookup_functional Hlookup2 Hlookup2');
          now (Tactics.subst_no_fail; Tactics.autoinjections)
      | HequivSigma : D.equivSigma ?S1 ?S2
      , Hfalse : forall _, ~ D.lookup ?S1 ?v _
      , Hlookup2 : D.lookup ?S2 ?v _ |- False =>
          destruct (proj2 HequivSigma _ _ Hlookup2) as [? [Hlookup1 []]];
          apply (Hfalse _ Hlookup1)
      | H : forall _ _ _, _ -> ~ _ |- False => eapply H; eassumption
      end
  | |- _ /\ _ =>
      intuition; [
        constructor; [reflexivity | assumption]
      |   match goal with
          | HequivSigma : D.equivSigma ?S1 ?S2
          , Hlookup1 : D.lookup ?s _ _ |- _ =>
              destruct (proj1 HequivSigma _ _ Hlookup1) as [[] [? []]];
              simpl in *; Tactics.subst_no_fail; Tactics.autoinjections;
              econstructor (eassumption)
          end
      ]
  end.
Qed.

(* Section 7: from well-typed to well-annotated (with a particular choice of annotation, namely 'concrete_annotation')  *)

Lemma typeOfLValue_wellAnnotatedLValue_aux {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e1 : expression A} :
  (forall {gtc}, 
     D.typeOfExpression S G e1 gtc ->
     exists e2 : expression genTypeCategory,
       D.equivExpression e1 e2 /\
       D.wellAnnotatedExpression (@concrete_annotation A) S G e2 gtc) ->
  forall {q} {t}, 
    D.typeOfLValue S G e1 q t ->
    exists e2 : expression genTypeCategory,
      D.equivExpression e1 e2 /\
      D.wellAnnotatedLValue (@concrete_annotation A) S G e2 q t.
Proof.
  intros typeOfExpression_wellAnnotatedExpression.
  inversion_clear 1.
  match goal with
  | H : D.typeOfExpression _ _ _ _ |- _ => destruct (typeOfExpression_wellAnnotatedExpression _ H) as [e2 []]
  end.
  exists e2; split; now my_auto.
Qed.

Lemma typeOfRValue_wellAnnotatedRValue_aux {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e1 : expression A} :
  (forall {gtc}, 
     D.typeOfExpression S G e1 gtc ->
     exists e2 : expression genTypeCategory,
       D.equivExpression e1 e2 /\
       D.wellAnnotatedExpression (@concrete_annotation A) S G e2 gtc) ->
  forall {gt},
    D.typeOfRValue S G e1 gt ->
    exists e2 : expression genTypeCategory,
      D.equivExpression e1 e2 /\
      D.wellAnnotatedRValue (@concrete_annotation A) S G e2 gt.
Proof.
  intros typeOfExpression_wellAnnotatedExpression.
  inversion_clear 1;
  match goal with
  | H : D.typeOfExpression _ _ _ _ |- _ => destruct (typeOfExpression_wellAnnotatedExpression _ H) as [e2 []]
  | H : D.typeOfLValue _ _ _ _ _ |- _ => destruct (typeOfLValue_wellAnnotatedLValue_aux typeOfExpression_wellAnnotatedExpression H) as [e2 []]
  end;
  exists e2; split; now my_auto.
Qed.

Lemma assignable_wellAnnotatedAssignee_aux {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e2 : expression A} :
  (forall {gtc},
     D.typeOfExpression S G e2 gtc ->
     exists e2' : expression genTypeCategory,
       D.equivExpression e2 e2' /\
       D.wellAnnotatedExpression (@concrete_annotation A) S G e2' gtc) ->
  forall {t1},
    D.assignable S G t1 e2 ->
    exists e2' : expression genTypeCategory,
      D.equivExpression e2 e2' /\
      D.wellAnnotatedAssignee (@concrete_annotation A) S G t1 e2'.
Proof.
  intros typeOfExpression_wellAnnotatedExpression.
  inversion_clear 1;
  match goal with
  | H : D.typeOfRValue _ _ _ _ |- _ => destruct (typeOfRValue_wellAnnotatedRValue_aux typeOfExpression_wellAnnotatedExpression H) as [e2' []]
  end;
  try match goal with
  | H : D.nullPointerConstant e2, Hequiv : D.equivExpression e2 _ |- _ => pose proof (nullPointerConstant_equiv Hequiv H)
  end;
  exists e2'; now my_auto.
Qed.

Lemma typeOfExpression_wellAnnotatedExpression {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e1 : expression A} {gtc} :
  D.typeOfExpression S G e1 gtc ->
  exists e2 : expression genTypeCategory,
    D.equivExpression e1 e2 /\
    D.wellAnnotatedExpression (@concrete_annotation A) S G e2 gtc.
Proof.
  revert e1 gtc.
  apply (
    expression_nrect
      (fun x => forall gtc (Ht : D.typeOfExpression' S G x gtc), exists y : expression' genTypeCategory, D.equivExpression' x y /\ D.wellAnnotatedExpression' (@concrete_annotation A) S G y gtc)
      (fun x => forall gtc (Ht : D.typeOfExpression S G x gtc), exists y : expression genTypeCategory, D.equivExpression x y /\ D.wellAnnotatedExpression (@concrete_annotation A) S G y gtc)
      (fun x => forall ps (Ht : D.typeOfArguments S G x ps), exists y : list (expression genTypeCategory), D.equivArguments x y /\ D.wellAnnotatedArguments (@concrete_annotation A) S G y ps)
  ); intros; inversion Ht; subst;
  repeat match goal with
  | IH : forall _, D.typeOfExpression _ _ ?e1 _ -> exists _, _
  , H  : D.typeOfExpression _ _ ?e1 _ |- _ => destruct (IH _ H) as [? []]; clear H
  | IH : forall _, D.typeOfExpression' _ _ ?e1 _ -> exists _, _
  , H  : D.typeOfExpression' _ _ ?e1 _ |- _ => destruct (IH _ H) as [? []]; clear H
  | IH : forall _, D.typeOfArguments _ _ ?es1 _ -> exists _, _
  , H  : D.typeOfArguments _ _ ?es1 _ |- _ => destruct (IH _ H) as [? []]; clear H
  | IH : forall _, D.typeOfExpression _ _ ?e1 _ -> exists _, _
  , H  : D.typeOfLValue _ _ ?e1 _ _ |- _ => destruct (typeOfLValue_wellAnnotatedLValue_aux IH H) as [? []]; clear H
  | IH : forall _, D.typeOfExpression _ _ ?e1 _ -> exists _, _
  , H  : D.typeOfRValue _ _ ?e1 _ |- _ => destruct (typeOfRValue_wellAnnotatedRValue_aux IH H) as [? []]; clear H
  | IH : forall _, D.typeOfExpression _ _ ?e1 _ -> exists _, _
  , H  : D.assignable _ _ _ ?e1 |- _ => destruct (assignable_wellAnnotatedAssignee_aux IH H) as [? []]; clear H
  end;
  eexists; split;
  econstructor (
    solve [
      eassumption
    | reflexivity
    | eapply nullPointerConstant_equiv; eassumption
    | match goal with
      | H : ~ D.nullPointerConstant ?e1, Hequiv : D.equivExpression ?e1 ?e2 |- ~ D.nullPointerConstant ?e2 =>
          intros ?; apply H; apply (nullPointerConstant_equiv (equivExpression_symm Hequiv)); assumption
      end
    ]
  ).
Qed.

Lemma typeOfRValue_wellAnnotatedRValue {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e1 : expression A} {gt} :
  D.typeOfRValue S G e1 gt ->
  exists e2 : expression genTypeCategory,
    D.equivExpression e1 e2 /\
    D.wellAnnotatedRValue (@concrete_annotation A) S G e2 gt.
Proof. exact (typeOfRValue_wellAnnotatedRValue_aux (fun gtc => typeOfExpression_wellAnnotatedExpression (gtc:=gtc))). Qed.   

Lemma assignable_wellAnnotatedAssignee {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {t1} {e2 : expression A} :
  D.assignable S G t1 e2 ->
  exists e2' : expression genTypeCategory,
    D.equivExpression e2 e2' /\
    D.wellAnnotatedAssignee (@concrete_annotation A) S G t1 e2'.
Proof. exact (assignable_wellAnnotatedAssignee_aux (fun gtc => typeOfExpression_wellAnnotatedExpression (gtc:=gtc))). Qed.

Lemma typeable_wellAnnotated {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {e1 : expression A} :
  D.typeable S G e1 ->
  exists e2 : expression genTypeCategory,
    D.equivExpression e1 e2 /\
    D.wellAnnotated (@concrete_annotation A) S G e2.
Proof.
  inversion_clear 1.
  match goal with
  | H : D.typeOfExpression _ _ _ _ |- _ =>
      destruct (typeOfExpression_wellAnnotatedExpression H) as [e2 []];
      exists e2; split; [assumption | econstructor; eassumption]
  end.
Qed.

Lemma wellTypedDefinition_wellAnnotatedDefinition {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {d1 : _ * expression A} :
  D.wellTypedDefinition S G d1 ->
  exists d2 : _ * expression genTypeCategory,
    D.equivDefinition d1 d2 /\
    D.wellAnnotatedDefinition (@concrete_annotation A) S G d2.
Proof.
  inversion_clear 1.
  match goal with
  | H : D.assignable _ _ _ _ |- _ =>
      destruct (assignable_wellAnnotatedAssignee H) as [? []];
      eexists; split; econstructor; eassumption
  end.
Qed.

Lemma wellTypedDeclaration_wellAnnotatedDeclaration {A B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {ds1 : list (_ * expression A)} :
  allList (D.wellTypedDefinition S G) ds1 ->
  exists ds2 : list (_ * expression genTypeCategory),
    D.equivDeclaration ds1 ds2 /\
    allList (D.wellAnnotatedDefinition (@concrete_annotation A) S G) ds2.
Proof.
  induction ds1;
  inversion_clear 1.
  - exists nil; split; constructor.
  - match goal with
    | H1 : D.wellTypedDefinition _ _ _
    , H2 : allList (D.wellTypedDefinition _ _) _ |- _ =>
        destruct (wellTypedDefinition_wellAnnotatedDefinition H1) as [? []];
        destruct (IHds1                                       H2) as [? []];
        eexists; split; econstructor; eassumption
    end.
Qed.

Lemma wellTypedStatement_wellAnnotatedStatement {A B B1 B2 : Set} {S : sigma B1 B2} {G : gamma} {t} {s1 : statement B A} :
  D.wellTypedStatement S G t s1 ->
  exists s2 : statement B genTypeCategory,
    D.equivStatement s1 s2 /\
    D.wellAnnotatedStatement (@concrete_annotation A) S G t s2.
Proof.
  revert G.
  apply (
    statement_nrect
      (fun x => forall G (Ht : D.wellTypedStatement' S G t x), exists y : statement' B genTypeCategory, D.equivStatement' x y /\ D.wellAnnotatedStatement' (@concrete_annotation A) S G t y)
      (fun x => forall G (Ht : D.wellTypedStatement S G t x), exists y : statement B genTypeCategory, D.equivStatement x y /\ D.wellAnnotatedStatement (@concrete_annotation A) S G t y)
      (fun x => forall G (Ht : allList (D.wellTypedStatement S G t) x), exists y : list (statement B genTypeCategory), D.equivBlock x y /\ allList (D.wellAnnotatedStatement (@concrete_annotation A) S G t) y)
  ); intros; inversion_clear Ht;
  repeat match goal with
  | H : allList (D.wellTypedDefinition _ _) ?ds |- _ =>
      match goal with
      | _ : D.equivDeclaration ds ?ds', _ : allList (D.wellAnnotatedDefinition _ _ _) ?ds' |- _ => fail 1
      | |- _ => destruct (wellTypedDeclaration_wellAnnotatedDeclaration H) as [? []]
      end
  | H : D.typeable _ _ ?e |- _ =>
      match goal with
      | _ : D.equivExpression e ?e', _ : D.wellAnnotated _ _ _ ?e' |- _ => fail 1
      | |- _ => destruct (typeable_wellAnnotated H) as [? []]
      end
  | H : D.typeOfRValue _ _ ?e _ |- _ =>
      match goal with
      | _ : D.equivExpression e ?e', _ : D.wellAnnotatedRValue _ _ _ ?e' _ |- _ => fail 1
      | |- _ => destruct (typeOfRValue_wellAnnotatedRValue H) as [? []]
      end
  | H : D.assignable _ _ _ ?e |- _ =>
      match goal with
      | _ : D.equivExpression e ?e', _ : D.wellAnnotatedAssignee _ _ _ _ ?e' |- _ => fail 1
      | |- _ => destruct (assignable_wellAnnotatedAssignee H) as [? []]
      end
  | IH : forall _, D.wellTypedStatement _ _ _ ?s -> _
  , H  : D.wellTypedStatement _ _ _ ?s |- _ =>
      match goal with
      | _ : D.equivStatement s ?s', _ : D.wellAnnotatedStatement _ _ _ _ ?s' |- _ => fail 1
      | |- _ => destruct (IH _ H) as [? []]
      end
  | IH : forall _, D.wellTypedStatement' _ _ _ ?s -> _
  , H  : D.wellTypedStatement' _ _ _ ?s |- _ =>
      match goal with
      | _ : D.equivStatement' s ?s', _ : D.wellAnnotatedStatement' _ _ _ _ ?s' |- _ => fail 1
      | |- _ => destruct (IH _ H) as [? []]
      end
  | IH : forall _, allList _ ?ss -> _
  , H  : allList (D.wellTypedStatement _ _ _) ?ss |- _ =>
      match goal with
      | _ : D.equivBlock ss ?ss', _ : allList _ ?ss' |- _ => fail 1
      | |- _ => destruct (IH _ H) as [? []]
      end
  end;
  eexists; split; econstructor (eassumption).
  Grab Existential Variables.
  assumption.
Qed.

Lemma wellTypedFunction_wellAnnotatedFunction {A B B1 B2 : Set} {S : sigma B1 B2} {p1 : _ * _ * statement B A} :
  D.wellTypedFunction S p1 ->
  exists p2 : _ * _ * statement B genTypeCategory,
    D.equivFunction p1 p2 /\
    D.wellAnnotatedFunction (@concrete_annotation A) S p2.
Proof.
  inversion_clear 1.
  match goal with
  | H : D.wellTypedStatement _ (Context.add_bindings ?bs _) ?t _ |- _ =>
      destruct (wellTypedStatement_wellAnnotatedStatement H) as [?s2 []];
      exists (t, bs, s2); split; constructor; assumption || reflexivity
  end.  
Qed.

Lemma wellTypedSigma_wellAnnotatedSigma {A B : Set} {S1 : sigma B A} :
  D.wellTypedSigma S1 ->
  exists S2 : sigma B genTypeCategory,
    D.equivSigma S1 S2 /\
    D.wellAnnotatedSigma (@concrete_annotation A) S2.
Proof.
  intros Ht1.
  pose proof (annotate_sigma_correct concrete_annotation S1) as Hcorrect.
  unfold annotate_sigma_spec in Hcorrect.
  unfold annotate_sigma in Hcorrect.
  pose proof (mapP_correct _ eq_identifier_correct (annotate_function_map_correct (B:=B) concrete_annotation S1) S1) as Hcorrect'.
  destruct (Context.mapP eq_identifier (fun _ : identifier => annotate_function concrete_annotation S1) S1); [now firstorder|].
  destruct Hcorrect' as [v [p1 [Hlookup1 [| [_ Hfalse]]]]]; [tauto|].
  pose proof (wellTypedFunction_wellAnnotatedFunction (Ht1 v p1 Hlookup1)).
  now firstorder.
Qed.

Lemma wellTypedProgram_wellAnnotatedProgram {A B : Set} {p1 : program B A} :
  D.wellTypedProgram p1 ->
  exists p2 : program B genTypeCategory,
    D.equivProgram p1 p2 /\
    D.wellAnnotatedProgram (@concrete_annotation A) p2.
Proof.
  inversion_clear 1.
  match goal with
  | Hlookup1 : D.lookup ?S1 _ _
  , Ht : D.wellTypedSigma ?S1 |- _ =>
      destruct (wellTypedSigma_wellAnnotatedSigma Ht) as [S2 [Hequiv Hannot]];
      destruct (proj1 Hequiv _ _ Hlookup1) as [[[] ?] [? HequivFunction]];
      inversion HequivFunction as []; simpl in *; Tactics.subst_no_fail; Tactics.autoinjections
  end.
  eexists; split; econstructor; reflexivity || eassumption.
Qed.

Lemma annotate_program_wellTypedProgram {A1 A2 B : Set} (A : annotation A1 A2) (p : program B A1) :
  boolSpec (if annotate_program A p then true else false) (D.wellTypedProgram p).
Proof.
  pose proof (annotate_program_correct A p) as Hcorrect.
  unfold annotate_program_spec in Hcorrect.
  destruct (annotate_program A p); intuition.
  - eapply wellTypedProgram_equiv.
    eapply equivProgram_symm; eassumption.
    eapply wellAnnotatedProgram_wellTypedProgram; eassumption.
  - intros Ht.
    pose proof (wellTypedProgram_wellAnnotatedProgram Ht).
    now firstorder.
Qed.

(* Section 8: identical (up to annotations) well-annotated expressions agree on type annotations *)

Lemma wellAnnotatedExpression_functional {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1_1 A2_1 A1_2 A2_2} {A1 : annotation A1_1 A2_1} {A2 : annotation A1_2 A2_2} {e1} {e2} {gtc1 gtc2},
    D.equivExpression e1 e2 ->
    D.wellAnnotatedExpression A1 S G e1 gtc1 ->
    D.wellAnnotatedExpression A2 S G e2 gtc2 ->
    gtc1 = gtc2.
Proof.
  intros Hdisjoint ? ? ? ? ? ? ? ? ? ? Hequiv H1 H2.
  pose proof (annotate_expression_correct Hdisjoint concrete_annotation e1) as Hcorrect.
  unfold annotate_expression_spec in Hcorrect.
  destruct (annotate_expression concrete_annotation S G e1).
  + destruct Hcorrect as [_ [_ Hunique]].
    pose proof (Hunique _ _ _ _ _ (equivExpression_refl _) H1).
    pose proof (Hunique _ _ _ _ _ Hequiv H2).
    congruence.
  + exfalso; eapply Hcorrect; eassumption.
Qed.

Lemma typeOfExpression_functional {A1 B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {e : expression A1} {gtc1 gtc2},
    D.typeOfExpression S G e gtc1 ->
    D.typeOfExpression S G e gtc2 ->
    gtc1 = gtc2.
Proof.
  intros Hdisjoint e ? ? H1 H2.
  destruct (typeOfExpression_wellAnnotatedExpression H1) as [? [Hequiv1 H1']].
  destruct (typeOfExpression_wellAnnotatedExpression H2) as [? [Hequiv2 H2']].
  exact (wellAnnotatedExpression_functional Hdisjoint (equivExpression_trans (equivExpression_symm Hequiv1) Hequiv2) H1' H2').
Qed.

Lemma wellAnnotatedRValue_functional {B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {A1_1 A2_1 A1_2 A2_2} {A1 : annotation A1_1 A2_1} {A2 : annotation A1_2 A2_2} {e1} {e2} {gt1 gt2},
    D.equivExpression e1 e2 ->
    D.wellAnnotatedRValue A1 S G e1 gt1 ->
    D.wellAnnotatedRValue A2 S G e2 gt2 ->
    gt1 = gt2.
Proof.
  intros Hdisjoint ? ? ? ? ? ? ? ? ? ? Hequiv H1 H2.
  generalize (annotate_rvalue_correct Hdisjoint concrete_annotation e1) as Hcorrect.
  unfold annotate_rvalue_spec.
  destruct (annotate_rvalue concrete_annotation S G e1). 
  + context_destruct.
    intros [_ [_ Hunique]].
    pose proof (Hunique _ _ _ _ _ (equivExpression_refl _) H1).
    pose proof (Hunique _ _ _ _ _ Hequiv H2).
    congruence.
  + intros Hcorrect; exfalso; eapply Hcorrect; eassumption.
Qed.

Lemma typeOfRValue_functional {A1 B1 B2 : Set} {S : sigma B1 B2} {G} :
  D.disjoint G S ->
  forall {e : expression A1} {gt1 gt2},
    D.typeOfRValue S G e gt1 ->
    D.typeOfRValue S G e gt2 ->
    gt1 = gt2.
Proof.
  intros Hdisjoint e ? ? H1 H2.
  destruct (typeOfRValue_wellAnnotatedRValue H1) as [? [Hequiv1 H1']].
  destruct (typeOfRValue_wellAnnotatedRValue H2) as [? [Hequiv2 H2']].
  exact (wellAnnotatedRValue_functional Hdisjoint (equivExpression_trans (equivExpression_symm Hequiv1) Hequiv2) H1' H2').
Qed.

(* Section 9: given an implementation P, if a program can be typed in the implementation-independent type system, then it can also be typed in the concrete type system assuming all constants are typeable under P *)

Lemma typeOfLValue_interpret_aux {P} {A B1 B2 : Set} {S : sigma B1 B2} {G} {e : expression A} {q} {t} :
  (forall {gtc},
     (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
     D.typeOfExpression S G e gtc ->
     exists tc,
       D.interpretGenTypeCategory P gtc tc /\
       AilTyping_defns.typeOfExpression P S G e tc) ->
  (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
  D.typeOfLValue S G e q t ->
  AilTyping_defns.typeOfLValue P S G e q t.
Proof.
  intros typeOfExpression_interpret HtypeableConstants.
  inversion_clear 1.
  match goal with
  | H : D.typeOfExpression S G e _ |- _ =>
      destruct (typeOfExpression_interpret _ HtypeableConstants H) as [? [Hinterp ?]];
      inversion Hinterp; subst; clear Hinterp
  end.
  econstructor; eassumption.
Qed.

Lemma typeOfRValue_interpret_aux {P} {A B1 B2 : Set} {S : sigma B1 B2} {G} {e : expression A} {gt} :
  (forall {gtc},
     (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
     D.typeOfExpression S G e gtc ->
     exists tc,
       D.interpretGenTypeCategory P gtc tc /\
       AilTyping_defns.typeOfExpression P S G e tc) ->
  (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
  D.typeOfRValue S G e gt ->
  exists t,
    D.interpretGenType P gt t /\
    AilTyping_defns.typeOfRValue P S G e t.
Proof.
  intros typeOfExpression_interpret HtypeableConstants.
  inversion_clear 1;
  match goal with
  | H : D.typeOfExpression S G ?e _ |- _ => destruct (typeOfExpression_interpret _ HtypeableConstants H) as [? []] 
  | H : D.typeOfLValue S G ?e _ _   |- _ => pose proof (typeOfLValue_interpret_aux typeOfExpression_interpret HtypeableConstants H)
  end;
  repeat match goal with
  | Hpt : D.pointerConversion ?gt1 ?gt2 |- _ =>
      match goal with
      | _ : D.interpretGenType P gt2 _ |- _ => fail 1
      | H : D.interpretGenType P gt1 _ |- _ => destruct (pointerConversion_interpret Hpt H) as [? []]
      | H : D.interpretGenTypeCategory P (GenRValueType gt1) _ |- _ => inversion H; subst
      | _ => fail
      end
  end;
  eexists; split; finish ltac:(solve [eassumption | eapply interpretGenType_inject]).
Qed.

Lemma assignable_interpret_aux {P} {A B1 B2 : Set} {S : sigma B1 B2} {G} {t1} {e2 : expression A} :
  (forall {gtc},
     (forall ic, D.constantExpressionContext ic e2 -> AilTyping_defns.typeableConstant P ic) ->
     D.typeOfExpression S G e2 gtc ->
     exists tc,
       D.interpretGenTypeCategory P gtc tc /\
       AilTyping_defns.typeOfExpression P S G e2 tc) ->
  (forall ic, D.constantExpressionContext ic e2 -> AilTyping_defns.typeableConstant P ic) ->
  D.assignable S G t1 e2 ->
  AilTyping_defns.assignable P S G t1 e2.
Proof.
  intros typeOfExpression_interpret HtypeableConstants.
  inversion_clear 1;
  match goal with
  | H : D.typeOfRValue S G _ _ |- _ => destruct (typeOfRValue_interpret_aux typeOfExpression_interpret HtypeableConstants H) as [? []]
  end;
  repeat match goal with
  | H : D.arithmetic ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.arithmetic t);
      pose proof (arithmetic_transport H Hinterp)
  | H : D.pointer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.pointer t);
      pose proof (pointer_interpret H Hinterp)
  | H : D.interpretGenType P (GenPointer _ _) ?t |- _ =>
      is_var t; inversion H; subst
  end;
  econstructor (eassumption).
Qed.

Lemma wellTypedBinaryArithmetic_transport {P} {gt1 gt2} {aop} {t1 t2} :
  D.interpretGenType P gt1 t1 ->
  D.interpretGenType P gt2 t2 ->
  D.wellTypedBinaryArithmetic gt1 aop gt2 ->
  A.wellTypedBinaryArithmetic t1  aop t2.
Proof.
  inversion_clear 3;
  repeat match goal with
  | H : D.arithmetic ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.arithmetic t);
      pose proof (arithmetic_transport H Hinterp)
  | H : D.integer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.integer t);
      pose proof (integer_transport H Hinterp)
  | H : D.pointer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.pointer t);
      pose proof (pointer_interpret H Hinterp)
  | H : D.interpretGenType P (GenPointer _ _) ?t |- _ =>
      is_var t; inversion H; subst
  end;
  econstructor (eassumption).
Qed.

Lemma typeableConstant_interpret {P} {ic} {git} {it} :
  D.typeOfConstant ic git ->
  A.typeOfConstant P ic it ->
  D.interpretGenIntegerType P git it.
Proof.
  inversion 1; subst;
  intros Ht1; try
  match goal with
  | _ : D.typeOfConstant ?ic (Concrete ?it)
  , Hmin : A.inMinIntegerRange _ ?it |- _ =>
    pose proof (Hmin P);
    assert (A.typeOfConstant P ic it) as Ht2
      by (econstructor (eassumption));
    pose proof (AilTyping_proof.typeOfConstant_functional Ht1 Ht2); subst;
    now constructor
  | _ : D.typeOfConstant ?ic (Unknown _) |- _ =>
    constructor; assumption
  | _ =>   inversion_clear Ht1; constructor
  end.
Qed.

Lemma typeOfExpression_interpret {P} {A B1 B2 : Set} {S : sigma B1 B2} {G} {e : expression A} {gtc} :
  (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
  D.typeOfExpression S G e gtc ->
  exists tc,
    D.interpretGenTypeCategory P gtc tc /\
    AilTyping_defns.typeOfExpression P S G e tc.
Proof.
  revert gtc.
  apply (
    expression_nrect
      (fun x => forall gtc (HtypeableConstants : forall ic, D.constantExpressionContext' ic x -> AilTyping_defns.typeableConstant P ic) (Ht : D.typeOfExpression' S G x gtc), exists tc, D.interpretGenTypeCategory P gtc tc /\ A.typeOfExpression' P S G x tc)
      (fun x => forall gtc (HtypeableConstants : forall ic, D.constantExpressionContext ic x -> AilTyping_defns.typeableConstant P ic) (Ht : D.typeOfExpression S G x gtc), exists tc, D.interpretGenTypeCategory P gtc tc /\ A.typeOfExpression P S G x tc)
      (fun x => forall ps (HtypeableConstants : forall ic, D.constantArgumentsContext ic x -> AilTyping_defns.typeableConstant P ic) (Ht : D.typeOfArguments S G x ps), A.typeOfArguments P S G x ps)
  ); intros;
  inversion Ht; subst;
  repeat match goal with
  | IH : forall _, _ -> D.typeOfExpression S G ?e _ -> _
  , H : D.typeOfRValue S G ?e _ |- _ =>
      match goal with
      | _ : A.typeOfRValue P S G e _ |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        destruct (typeOfRValue_interpret_aux IH HtypeableConstants' H) as [? []]
      end
  | IH : forall _, _ -> D.typeOfExpression S G ?e _ -> _
  , H : D.typeOfExpression S G ?e _ |- _ =>
      match goal with
      | _ : A.typeOfExpression P S G e _ |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        destruct (IH _ HtypeableConstants' H) as [? []]
      end
  | IH : forall _, _ -> D.typeOfExpression' S G ?e _ -> _
  , H : D.typeOfExpression' S G ?e _ |- _ =>
      match goal with
      | _ : A.typeOfExpression' P S G e _ |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext' ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        destruct (IH _ HtypeableConstants' H) as [? []]
      end
  | IH : forall _, _ -> D.typeOfArguments S G ?es _ -> _
  , H : D.typeOfArguments S G ?es _ |- _ =>
      match goal with
      | _ : A.typeOfArguments P S G es _ |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantArgumentsContext ic es -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (IH _ HtypeableConstants' H)
      end
  | IH : forall _, _ -> D.typeOfExpression S G ?e _ -> _
  , H : D.assignable S G _ ?e |- _ =>
      match goal with
      | _ : A.assignable P S G _ e |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (assignable_interpret_aux IH HtypeableConstants' H)
      end
  | IH : forall _, _ -> D.typeOfExpression S G ?e _ -> _
  , H : D.typeOfLValue S G ?e _ _ |- _ =>
      match goal with
      | _ : A.typeOfLValue P S G e _ _ |- _ => fail 1
      | _ =>
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (typeOfLValue_interpret_aux IH HtypeableConstants' H)
      end
  end;
  repeat match goal with
  | H : D.arithmetic ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.arithmetic t);
      pose proof (arithmetic_transport H Hinterp)
  | H : D.integer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.integer t);
      pose proof (integer_transport H Hinterp)
  | H : D.real ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.real t);
      pose proof (real_transport H Hinterp)
  | H : D.scalar ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.scalar t);
      pose proof (scalar_transport H Hinterp)
  | H : D.pointer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.pointer t);
      pose proof (pointer_interpret H Hinterp)
  | H : ~ D.pointer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (~ A.pointer t);
      assert (~ A.pointer t) by (let H' := fresh in intros H'; exact (H (pointer_inject Hinterp H')))
  | H : D.interpretGenType P (GenPointer _ _) ?t |- _ =>
      is_var t; inversion H; subst
  | H : D.interpretGenType P (GenFunction _ _) ?t |- _ =>
      is_var t; inversion H; subst
  | H : D.interpretGenTypeCategory P (GenRValueType _) ?tc |- _ =>
      is_var tc; inversion H; subst
  | H : D.interpretGenType P GenVoid ?t |- _ =>
      is_var t; inversion H; subst
  | H : D.promotion ?gt1 ?gt2, H1 : D.interpretGenType P ?gt1 _ |- _ =>
      match goal with
      | _ : D.interpretGenType P gt2 _ |- _ => fail 1
      | _ => destruct (promotion_interpret H H1) as [? []]
      end
  | H1 : D.interpretGenType P ?gt1 _
  , H2 : D.interpretGenType P ?gt2 _
  , H : D.usualArithmetic ?gt1 ?gt2 ?gt3 |- _ =>
      match goal with
      | _ : D.interpretGenType P gt3 _ |- _ => fail 1
      | _ => destruct (usualArithmetic_interpret H H1 H2) as [? []]
      end
  | H : D.typeOfConstant ?ic ?git |- _ =>
      match goal with
      | _ : D.interpretGenIntegerType P ?git _ |- _ => fail 1
      | _ =>
        let HtypeableConstant := fresh in
        assert (A.typeableConstant P ic) as HtypeableConstant
          by (apply (HtypeableConstants ic); constructor);
        let H' := fresh in
        destruct (AilTyping_proof.typeableConstant_typeOfConstant HtypeableConstant) as [? H'];
        pose proof (typeableConstant_interpret H H')
      end
  | H1 : D.interpretGenType P ?gt1 ?t1
  , H2 : D.interpretGenType P ?gt2 ?t2
  , H  : D.wellTypedBinaryArithmetic ?gt1 ?aop ?gt2 |- _ =>
      notHyp (A.wellTypedBinaryArithmetic t1 aop t2);
      pose proof (wellTypedBinaryArithmetic_transport H1 H2 H)
  | H : D.wellTypedBinaryArithmetic (inject_type ?t1) _ _ |- _ =>
     match goal with
     | _ : D.interpretGenType P (inject_type t1) _ |- _ => fail 1
     | _ => pose proof (interpretGenType_inject P t1)
     end
  | H : D.wellTypedBinaryArithmetic _ _ (inject_type ?t2) |- _ =>
     match goal with
     | _ : D.interpretGenType P (inject_type t2) _ |- _ => fail 1
     | _ => pose proof (interpretGenType_inject P t2)
     end
  end;
  match goal with
  | |- exists _, _ => eexists; split
  | _ => idtac
  end;
  solve [
    econstructor (
      solve [
        eassumption
      | repeat constructor; solve [eassumption|eapply interpretGenType_inject]
      ]
    )
  | eassumption
  ].
Qed.

Lemma typeOfRValue_interpret {A B1 B2 : Set} {S : sigma B1 B2} {G} {e : expression A} {gt} {P} :
  (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
  D.typeOfRValue S G e gt ->
  exists t,
    D.interpretGenType P gt t /\
    AilTyping_defns.typeOfRValue P S G e t.
Proof.
  eapply typeOfRValue_interpret_aux.
  eapply @typeOfExpression_interpret.
Qed.

Lemma typeable_interpret {A B1 B2 : Set} {S : sigma B1 B2} {G} {e : expression A} {P} :
  (forall ic, D.constantExpressionContext ic e -> AilTyping_defns.typeableConstant P ic) ->
  D.typeable S G e ->
  AilTyping_defns.typeable P S G e.
Proof.
  intros HtypeableConstants.
  inversion_clear 1.
  match goal with
  | H : D.typeOfExpression _ _ _ _ |- _ =>
      destruct (typeOfExpression_interpret HtypeableConstants H) as [? []]
  end.
  econstructor.
  eassumption.
Qed.

Lemma assignable_interpret {A B1 B2 : Set} {S : sigma B1 B2} {G} {t1} {e2 : expression A} {P} :
  (forall ic, D.constantExpressionContext ic e2 -> AilTyping_defns.typeableConstant P ic) ->
  D.assignable S G t1 e2 ->
  AilTyping_defns.assignable P S G t1 e2.
Proof.
  eapply assignable_interpret_aux.
  eapply @typeOfExpression_interpret.
Qed.

Lemma wellTypedDefinition_interpret {A B1 B2 : Set} {S : sigma B1 B2} {G} {d : _ * expression A} {P} :
  (forall ic, D.constantDefinitionContext ic d -> AilTyping_defns.typeableConstant P ic) ->
  D.wellTypedDefinition S G d ->
  AilTyping_defns.wellTypedDefinition P S G d.
Proof.
  intros HtypeableConstants.
  inversion 1; subst.
  match goal with
  | H : D.assignable _ _ _ _ |- _ =>
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
      pose proof (assignable_interpret HtypeableConstants' H)
  end.
  econstructor; eassumption.
Qed.

Lemma wellTypedDeclaration_interpret {A B1 B2 : Set} {S : sigma B1 B2} {G} {ds : list (_ * expression A)} {P} :
  (forall ic, D.constantDeclarationContext ic ds -> AilTyping_defns.typeableConstant P ic) ->
  allList (D.wellTypedDefinition S G) ds ->
  allList (AilTyping_defns.wellTypedDefinition P S G) ds.
Proof.
  induction ds;
  intros HtypeableConstants;
  inversion_clear 1.
  - constructor.
  - match goal with
    | H : D.wellTypedDefinition _ _ ?d |- _ =>
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantDefinitionContext ic d -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (wellTypedDefinition_interpret HtypeableConstants' H)
    end.
    match goal with
    | H : allList (D.wellTypedDefinition _ _) ?ds |- _ =>
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantDeclarationContext ic ds -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (IHds HtypeableConstants' H)
    end.
    econstructor; eassumption.
Qed.

Lemma wellTypedStatement_interpret {A B B1 B2 : Set} {S : sigma B1 B2} {G} {t} {s : statement B A} {P} :
  (forall ic, D.constantStatementContext ic s -> AilTyping_defns.typeableConstant P ic) ->
  D.wellTypedStatement S G t s ->
  AilTyping_defns.wellTypedStatement P S G t s.
Proof.
  revert G.
  apply (
    statement_nrect
      (fun x => forall G (HtypeableConstants : forall ic, D.constantStatementContext' ic x -> AilTyping_defns.typeableConstant P ic) (Ht : D.wellTypedStatement' S G t x), A.wellTypedStatement' P S G t x)
      (fun x => forall G (HtypeableConstants : forall ic, D.constantStatementContext ic x -> AilTyping_defns.typeableConstant P ic) (Ht : D.wellTypedStatement S G t x), A.wellTypedStatement P S G t x)
      (fun x => forall G (HtypeableConstants : forall ic, D.constantBlockContext ic x -> AilTyping_defns.typeableConstant P ic) (Ht : allList (D.wellTypedStatement S G t) x), allList (A.wellTypedStatement P S G t) x)
  ); intros;
  inversion Ht; subst;
  repeat match goal with
  | IH : forall _, _ -> D.wellTypedStatement S _ _ ?s -> _
  , H : D.wellTypedStatement S _ _ ?s |- _ =>
      match goal with
      | _ : A.wellTypedStatement P S _ _ s |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantStatementContext ic s -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (IH _ HtypeableConstants' H)
      end
  | IH : forall _, _ -> allList (D.wellTypedStatement S _ _) ?ss -> _
  , H : allList (D.wellTypedStatement S _ _) ?ss |- _ =>
      match goal with
      | _ : allList (A.wellTypedStatement P S _ _) ss |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantBlockContext ic ss -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (IH _ HtypeableConstants' H)
      end
  | IH : forall _, _ -> D.wellTypedStatement' S _ _ ?s -> _
  , H : D.wellTypedStatement' S _ _ ?s |- _ =>
      match goal with
      | _ : A.wellTypedStatement' P S _ _ s |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantStatementContext' ic s -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (IH _ HtypeableConstants' H)
      end
  | H : D.typeOfRValue S _ ?e _ |- _ =>
      match goal with
      | _ : A.typeOfRValue P S _ e _ |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        destruct (typeOfRValue_interpret HtypeableConstants' H) as [? []]
      end
  | H : D.typeable S _ ?e |- _ =>
      match goal with
      | _ : A.typeable P S _ e |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (typeable_interpret HtypeableConstants' H)
      end
  | H : D.assignable S _ _ ?e |- _ =>
      match goal with
      | _ : A.assignable P S _ _ e |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantExpressionContext ic e -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (assignable_interpret HtypeableConstants' H)
      end
  | H : D.typeOfConstant ?ic ?git |- _ =>
      match goal with
      | _ : D.interpretGenIntegerType P ?git _ |- _ => fail 1
      | _ =>
        let HtypeableConstant := fresh in
        assert (A.typeableConstant P ic) as HtypeableConstant
          by (apply (HtypeableConstants ic); constructor);
        let H' := fresh in
        destruct (AilTyping_proof.typeableConstant_typeOfConstant HtypeableConstant) as [? H'];
        pose proof (typeableConstant_interpret H H')
      end
  | H : allList (D.wellTypedDefinition S _) ?ds |- _ =>
      match goal with
      | _ : allList (A.wellTypedDefinition P S _) ds |- _ => fail 1
      | _ => 
        let HtypeableConstants' := fresh in
        assert (forall ic, D.constantDeclarationContext ic ds -> A.typeableConstant P ic) as HtypeableConstants'
          by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
        pose proof (wellTypedDeclaration_interpret HtypeableConstants' H)
      end
  end;
  repeat match goal with
  | H : D.integer ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.integer t);
      pose proof (integer_transport H Hinterp)
  | H : D.scalar ?gt, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (A.scalar t);
      pose proof (scalar_transport H Hinterp)
  end;
  econstructor (eassumption).
Qed.

Lemma wellTypedFunction_interpret {A B B1 B2 : Set} {S : sigma B1 B2} {p : _ * _ * statement B A} {P} :
  (forall ic, D.constantFunctionContext ic p -> AilTyping_defns.typeableConstant P ic) ->
  D.wellTypedFunction S p ->
  AilTyping_defns.wellTypedFunction P S p.
Proof.
  intros HtypeableConstants.
  inversion 1; subst.
  match goal with
  | H : D.wellTypedStatement _ _ _ ?s |- _ =>
      let HtypeableConstants' := fresh in
      assert (forall ic, D.constantStatementContext ic s -> A.typeableConstant P ic) as HtypeableConstants'
        by (let ic := fresh in intros ic ?; apply (HtypeableConstants ic); econstructor (assumption));
      pose proof (wellTypedStatement_interpret HtypeableConstants' H)
  end.
  econstructor; eassumption.
Qed.

Lemma wellTypedSigma_interpret {A B : Set} {S : sigma B A} {P} :
  (forall ic, D.constantSigmaContext ic S -> AilTyping_defns.typeableConstant P ic) ->
  D.wellTypedSigma S ->
  AilTyping_defns.wellTypedSigma P S.
Proof.
  intros HtypeableConstants Ht.
  intros v p Hlookup.
  eapply wellTypedFunction_interpret.
  - intros ic ?.
    apply (HtypeableConstants ic).
    econstructor (eassumption).
  - eapply Ht; eassumption.
Qed.

Lemma wellTypedProgram_interpret {A B : Set} {p : program B A} {P} :
  (forall ic, D.constantProgramContext ic p -> AilTyping_defns.typeableConstant P ic) ->
  D.wellTypedProgram p ->
  AilTyping_defns.wellTypedProgram P p.
Proof.
  intros HtypeableConstants.
  inversion 1; subst.
  econstructor.
  - eassumption.
  - eapply wellTypedSigma_interpret.
    + intros ic ?.
      apply (HtypeableConstants ic).
      econstructor (eassumption).
    + eassumption.
Qed.

(* Section 10: if a program has a typing for some implementation, then it has a typing in the implementation-independent system *)

Lemma typeableConstant_inject {P} {ic} {it} :
  A.typeOfConstant P ic it ->
  exists git,
    D.interpretGenIntegerType P git it /\
    D.typeOfConstant ic git.
Proof.
  pose proof (type_of_constant_correct ic).
  exists (type_of_constant ic); split.
  - eapply typeableConstant_interpret; eassumption.
  - assumption.
Qed.

Lemma wellTypedBinaryArithmetic_inject {P} {gt1 gt2} {aop} {t1 t2} :
  D.interpretGenType P gt1 t1 ->
  D.interpretGenType P gt2 t2 ->
  A.wellTypedBinaryArithmetic t1  aop t2 ->
  D.wellTypedBinaryArithmetic gt1 aop gt2.
Proof.
  inversion_clear 3;
  repeat match goal with
  | H : A.arithmetic ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.arithmetic gt);
      pose proof (arithmetic_inject Hinterp H)
  | H : A.integer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.integer gt);
      pose proof (integer_inject Hinterp H)
  end;
  econstructor (eassumption).
Qed.

Lemma typeOfLValue_inject_aux {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {e : expression A} {q} {t} :
  (forall {tc},
     AilTyping_defns.typeOfExpression P S G e tc ->
     exists gtc,
       D.interpretGenTypeCategory P gtc tc /\
       D.typeOfExpression S G e gtc) ->
  AilTyping_defns.typeOfLValue P S G e q t ->
  D.typeOfLValue S G e q t.
Proof.
  intros typeOfExpression_interpret.
  inversion_clear 1.
  match goal with
  | H : A.typeOfExpression _ _ _ _ _ |- _ =>
      destruct (typeOfExpression_interpret _ H) as [? [Hinterp ?]];
      inversion Hinterp; subst
  end.
  econstructor; eassumption.
Qed.

Lemma typeOfRValue_inject_aux {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {e : expression A} {t} :
  (forall {tc},
     AilTyping_defns.typeOfExpression P S G e tc ->
     exists gtc,
       D.interpretGenTypeCategory P gtc tc /\
       D.typeOfExpression S G e gtc) ->
  AilTyping_defns.typeOfRValue P S G e t ->
  exists gt,
    D.interpretGenType P gt t /\
    D.typeOfRValue S G e gt.
Proof.
  intros typeOfExpression_interpret.
  inversion_clear 1;
  match goal with
  | H : A.typeOfExpression _ _ _ _ _ |- _ => destruct (typeOfExpression_interpret _ H) as [? [? ?]]
  | H : A.typeOfLValue _ _ _ _ _ _ |- _ => pose proof (typeOfLValue_inject_aux typeOfExpression_interpret H)
  end;
  repeat match goal with
  | Hpt : A.pointerConversion ?t1 ?t2 |- _ =>
      match goal with
      | _ : D.interpretGenType P _ t2 |- _ => fail 1
      | H : D.interpretGenType P _ t1 |- _ => destruct (pointerConversion_inject Hpt H) as [? []]
      | H : D.interpretGenTypeCategory P _ (RValueType t1) |- _ => inversion H; subst
      | _ => fail
      end
  end;
  eexists; (split; [solve [eassumption | eapply interpretGenType_inject] | econstructor (eassumption)]).
Qed.

Lemma assignable_inject_aux {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {t1} {e2 : expression A} :
  (forall {tc},
     AilTyping_defns.typeOfExpression P S G e2 tc ->
     exists gtc,
       D.interpretGenTypeCategory P gtc tc /\
       D.typeOfExpression S G e2 gtc) ->
  AilTyping_defns.assignable P S G t1 e2 ->
  D.assignable S G t1 e2.
Proof.
  intros typeOfExpression_inject.
  inversion_clear 1;
  match goal with
  | H : A.typeOfRValue P S G _ _ |- _ => destruct (typeOfRValue_inject_aux typeOfExpression_inject H) as [? []]
  end;
  repeat match goal with
  | H : A.arithmetic ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.arithmetic gt);
      pose proof (arithmetic_inject Hinterp H)
  | H : A.pointer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.pointer gt);
      pose proof (pointer_inject Hinterp H)
  | H : D.interpretGenType P ?gt (Pointer _ _) |- _ =>
      is_var gt; inversion H; subst
  end;
  econstructor (eassumption).
Qed.

Lemma typeOfExpression_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {e : expression A} {tc} :
  AilTyping_defns.typeOfExpression P S G e tc ->
  exists gtc,
    D.interpretGenTypeCategory P gtc tc /\
    D.typeOfExpression S G e gtc.
Proof.
  revert tc.
  apply (
    expression_nrect
      (fun x => forall tc (Ht : A.typeOfExpression' P S G x tc), exists gtc, D.interpretGenTypeCategory P gtc tc /\ D.typeOfExpression' S G x gtc)
      (fun x => forall tc (Ht : A.typeOfExpression P S G x tc), exists gtc, D.interpretGenTypeCategory P gtc tc /\ D.typeOfExpression S G x gtc)
      (fun x => forall ps (Ht : A.typeOfArguments P S G x ps), D.typeOfArguments S G x ps)
  ); intros;
  inversion Ht; subst;


  repeat match goal with
  | IH : forall _, A.typeOfExpression P S G ?e _ -> _
  , H : A.typeOfRValue P S G ?e _ |- _ =>
      match goal with
      | _ : D.typeOfRValue S G e _ |- _ => fail 1
      | _ => destruct (typeOfRValue_inject_aux IH H) as [? []]
      end
  | IH : forall _, A.typeOfExpression P S G ?e _ -> _
  , H : A.typeOfExpression P S G ?e _ |- _ =>
      match goal with
      | _ : D.typeOfExpression S G e _ |- _ => fail 1
      | _ => destruct (IH _ H) as [? []]
      end
  | IH : forall _, A.typeOfExpression' P S G ?e _ -> _
  , H : A.typeOfExpression' P S G ?e _ |- _ =>
      match goal with
      | _ : D.typeOfExpression' S G e _ |- _ => fail 1
      | _ => destruct (IH _ H) as [? []]
      end
  | IH : forall _, A.typeOfArguments P S G ?es _ -> _
  , H : A.typeOfArguments P S G ?es _ |- _ =>
      match goal with
      | _ : D.typeOfArguments S G es _ |- _ => fail 1
      | _ => pose proof (IH _ H)
      end
  | IH : forall _, A.typeOfExpression P S G ?e _ -> _
  , H : A.assignable P S G _ ?e |- _ =>
      match goal with
      | _ : D.assignable S G _ e |- _ => fail 1
      | _ => pose proof (assignable_inject_aux IH H)
      end
  | IH : forall _, A.typeOfExpression P S G ?e _ -> _
  , H : A.typeOfLValue P S G ?e _ _ |- _ =>
      match goal with
      | _ : D.typeOfLValue S G e _ _ |- _ => fail 1
      | _ => pose proof (typeOfLValue_inject_aux IH H)
      end
  end;

  repeat match goal with
  | H : A.arithmetic ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.arithmetic gt);
      pose proof (arithmetic_inject Hinterp H)
  | H : A.integer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.integer gt);
      pose proof (integer_inject Hinterp H)
  | H : A.real ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.real gt);
      pose proof (real_inject Hinterp H)
  | H : A.scalar ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.scalar gt);
      pose proof (scalar_inject Hinterp H)
  | H : A.pointer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.pointer gt);
      pose proof (pointer_inject Hinterp H)
  | H : ~ A.pointer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (~ D.pointer gt);
      assert (~ D.pointer gt) by (let H' := fresh in intros H'; exact (H (pointer_interpret H' Hinterp)))
  | H : D.interpretGenType P ?gt (Pointer _ _) |- _ =>
      is_var gt; inversion H; subst
  | H : D.interpretGenType P ?gt (Function _ _) |- _ =>
      is_var gt; inversion H; subst
  | H : D.interpretGenTypeCategory P ?gtc (RValueType _) |- _ =>
      is_var gtc; inversion H; subst
  | H : D.interpretGenType P ?gt Void |- _ =>
      is_var gt; inversion H; subst
  | H : A.promotion P ?t1 ?t2, H1 : D.interpretGenType P _ ?t1 |- _ =>
      match goal with
      | _ : D.interpretGenType P _ t2 |- _ => fail 1
      | _ => destruct (promotion_inject H H1) as [? []]
      end
  | H1 : D.interpretGenType P _ ?t1
  , H2 : D.interpretGenType P _ ?t2
  , H : A.usualArithmetic P ?t1 ?t2 ?t3 |- _ =>
      match goal with
      | _ : D.interpretGenType P _ t3 |- _ => fail 1
      | _ => destruct (usualArithmetic_inject H H1 H2) as [? []]
      end
  | H : A.typeOfConstant P ?ic ?it |- _ =>
      match goal with
      | _ : D.interpretGenIntegerType P _ ?it |- _ => fail 1
      | _ => destruct (typeOfConstant_inject H) as [? []]
      end
  | H1 : D.interpretGenType P ?gt1 ?t1
  , H2 : D.interpretGenType P ?gt2 ?t2
  , H  : A.wellTypedBinaryArithmetic ?t1 ?aop ?t2 |- _ =>
      notHyp (D.wellTypedBinaryArithmetic gt1 aop gt2);
      pose proof (wellTypedBinaryArithmetic_inject H1 H2 H)
  | H : A.wellTypedBinaryArithmetic ?t1 _ _ |- _ =>
     match goal with
     | _ : D.interpretGenType P _ t1 |- _ => fail 1
     | _ => pose proof (interpretGenType_inject P t1)
     end
  | H : A.wellTypedBinaryArithmetic _ _ ?t2 |- _ =>
     match goal with
     | _ : D.interpretGenType P _ t2 |- _ => fail 1
     | _ => pose proof (interpretGenType_inject P t2)
     end
  end;

  try now match goal with
  | |- exists _, _ => eexists; split
  | _ => idtac
  end;
  solve [
    econstructor (
      solve [
        eassumption
      | match goal with
        | |- D.interpretGenType P _ (Basic (Integer (size_t P))) => do 2 constructor; eapply D.InterpretGenIntegerType_SizeT
        | |- D.interpretGenType P _ (Basic (Integer (ptrdiff_t P))) => do 2 constructor; eapply D.InterpretGenIntegerType_PtrdiffT
        | _ : A.typeOfExpression' P S G (Var _) (RValueType (type_from_sigma ?p)) |- D.interpretGenType P _ (type_from_sigma ?p) => eapply interpretGenType_inject
        | _ => solve [repeat first [eassumption | constructor] | eapply interpretGenType_inject]
        end
      | reflexivity
      ]
    )
  | eassumption
  ].
Qed.

Lemma typeOfRValue_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {e : expression A} {t} :
  AilTyping_defns.typeOfRValue P S G e t ->
  exists gt,
    D.interpretGenType P gt t /\
    D.typeOfRValue S G e gt.
Proof.
  eapply typeOfRValue_inject_aux.
  eapply @typeOfExpression_inject.
Qed.

Lemma assignable_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {t1} {e2 : expression A} :
  AilTyping_defns.assignable P S G t1 e2 ->
  D.assignable S G t1 e2.
Proof.
  eapply assignable_inject_aux.
  eapply @typeOfExpression_inject.
Qed.

Lemma typeable_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {e : expression A} :
  AilTyping_defns.typeable P S G e ->
  D.typeable S G e.
Proof.
  inversion_clear 1.
  match goal with
  | H : A.typeOfExpression _ _ _ _ _ |- _ => destruct (typeOfExpression_inject H) as [? []]
  end.
  econstructor; eassumption.
Qed.

Lemma wellTypedDefinition_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {d : _ * expression A} :
  AilTyping_defns.wellTypedDefinition P S G d ->
  D.wellTypedDefinition S G d.
Proof.
  inversion 1; subst.
  match goal with
  | H : A.assignable _ _ _ _ _ |- _ => pose proof (assignable_inject H)
  end.
  econstructor; eassumption.
Qed.

Lemma wellTypedDeclaration_inject {A B1 B2 : Set} {P} {S : sigma B1 B2} {G} {ds : list (_ * expression A)} :
  allList (AilTyping_defns.wellTypedDefinition P S G) ds ->
  allList (D.wellTypedDefinition S G) ds.
Proof.
  induction ds;
  inversion_clear 1.
  - constructor.
  - match goal with
    | H : A.wellTypedDefinition _ _ _ ?d |- _ => pose proof (wellTypedDefinition_inject H)
    end.
    match goal with
    | H : allList (A.wellTypedDefinition _ _ _) ?ds |- _ => pose proof (IHds H)
    end.
    econstructor; eassumption.
Qed.

Lemma wellTypedStatement_inject {A B B1 B2 : Set} {P} {S : sigma B1 B2} {G} {t} {s : statement B A} :
  AilTyping_defns.wellTypedStatement P S G t s ->
  D.wellTypedStatement S G t s.
Proof.
  revert G.
  apply (
    statement_nrect
      (fun x => forall G (Ht : A.wellTypedStatement' P S G t x), D.wellTypedStatement' S G t x)
      (fun x => forall G (Ht : A.wellTypedStatement P S G t x), D.wellTypedStatement S G t x)
      (fun x => forall G (Ht : allList (A.wellTypedStatement P S G t) x), allList (D.wellTypedStatement S G t) x)
  ); intros;
  inversion Ht; subst;
  repeat match goal with
  | IH : forall _, A.wellTypedStatement P S _ _ ?s -> _
  , H : A.wellTypedStatement P S _ _ ?s |- _ =>
      match goal with
      | _ : D.wellTypedStatement S _ _ s |- _ => fail 1
      | _ => pose proof (IH _ H)
      end
  | IH : forall _, allList (A.wellTypedStatement P S _ _) ?ss -> _
  , H : allList (A.wellTypedStatement P S _ _) ?ss |- _ =>
      match goal with
      | _ : allList (D.wellTypedStatement S _ _) ss |- _ => fail 1
      | _ => pose proof (IH _ H)
      end
  | IH : forall _, A.wellTypedStatement' P S _ _ ?s -> _
  , H : A.wellTypedStatement' P S _ _ ?s |- _ =>
      match goal with
      | _ : D.wellTypedStatement' S _ _ s |- _ => fail 1
      | _ => pose proof (IH _ H)
      end
  | H : A.typeOfRValue P S _ ?e _ |- _ =>
      match goal with
      | _ : D.typeOfRValue S _ e _ |- _ => fail 1
      | _ => destruct (typeOfRValue_inject H) as [? []]
      end
  | H : A.typeable P S _ ?e |- _ =>
      match goal with
      | _ : D.typeable S _ e |- _ => fail 1
      | _ => pose proof (typeable_inject H)
      end
  | H : A.assignable P S _ _ ?e |- _ =>
      match goal with
      | _ : D.assignable S _ _ e |- _ => fail 1
      | _ => pose proof (assignable_inject H)
      end
  | H : A.typeOfConstant P ?ic ?it |- _ =>
      match goal with
      | _ : D.interpretGenIntegerType P _ ?it |- _ => fail 1
      | _ => destruct (typeOfConstant_inject H) as [? []]
      end
  | H : allList (A.wellTypedDefinition P S _) ?ds |- _ =>
      match goal with
      | _ : allList (D.wellTypedDefinition S _) ds |- _ => fail 1
      | _ => pose proof (wellTypedDeclaration_inject H)
      end
  end;
  repeat match goal with
  | H : A.integer ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.integer gt);
      pose proof (integer_inject Hinterp H)
  | H : A.scalar ?t, Hinterp : D.interpretGenType P ?gt ?t |- _ =>
      notHyp (D.scalar gt);
      pose proof (scalar_inject Hinterp H)
  end; try
  econstructor (eassumption).
Qed.

Lemma wellTypedFunction_inject {A B B1 B2 : Set} {P} {S : sigma B1 B2} {p : _ * _ * statement B A} :
  A.wellTypedFunction P S p ->
  D.wellTypedFunction S p.
Proof.
  inversion 1; subst.
  match goal with
  | H : A.wellTypedStatement _ _ _ _ ?s |- _ => pose proof (wellTypedStatement_inject H)
  end.
  econstructor; eassumption.
Qed.

Lemma wellTypedSigma_inject {A B : Set} {P} {S : sigma B A} :
  AilTyping_defns.wellTypedSigma P S ->
  D.wellTypedSigma S.
Proof.
  intros Ht.
  intros v p Hlookup.
  eapply wellTypedFunction_inject.
  eapply Ht; eassumption.
Qed.

Lemma wellTypedProgram_inject {A B : Set} {P} {S : program B A} :
  AilTyping_defns.wellTypedProgram P S ->
  D.wellTypedProgram S.
Proof.
  inversion 1; subst.
  econstructor.
  - eassumption.
  - eapply wellTypedSigma_inject; eassumption.
Qed.

