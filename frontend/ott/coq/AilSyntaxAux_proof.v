Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux AilTypesAux_proof.
Require Import AilSyntax AilSyntax_proof.
Require Import AilSyntaxAux.

Module D.
Require AilSyntaxAux_defns.
Include AilSyntax_defns.
Include AilSyntaxAux_defns.
End D.

Lemma fv_correct {A} v :
  forall x : expression A, boolSpec (fv v x) (D.fv v x).
Proof.
  apply (expression_nrect (fun x => boolSpec (fv'          v x) (D.fv'         v x))
                          (fun x => boolSpec (fv           v x) (D.fv          v x))
                          (fun x => boolSpec (fv_arguments v x) (D.fvArguments v x)));
  intros; unfold_goal; simpl; unfold orb; fold (@fv_arguments A);
  repeat match goal with
  | IH : boolSpec (fv ?v ?e) _ |- fv ?v ?e = _ -> _ => case_fun IH
  | IH : boolSpec (fv' ?v ?e) _ |- fv' ?v ?e = _ -> _ => case_fun IH
  | IH : boolSpec (fv_arguments ?v ?e) _ |- fv_arguments ?v ?e = _ -> _ => case_fun IH
  | |- eq_identifier ?x ?y = _ -> _ => case_fun (eq_identifier_correct x y)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma null_pointer_constant_correct {A} :
  forall x : expression A, boolSpec (null_pointer_constant x) (D.nullPointerConstant x).
Proof.
  apply (expression_nrect (fun x => boolSpec (null_pointer_constant' x) (D.nullPointerConstant' x))
                          (fun x => boolSpec (null_pointer_constant  x) (D.nullPointerConstant  x))
                          (fun x => True));
  intros; unfold boolSpec; simpl; unfold andb;
  repeat match goal with
  | IH : boolSpec _ _ |- _ => boolSpec_destruct
  | |- unqualified ?q = _ -> _ => case_fun (unqualified_correct q)
  | _ => context_destruct
  end; now my_auto.
Qed.

Lemma nullPointerConstant_equiv {A1 A2} :
  forall {e1 : expression A1} {e2 : expression A2},
    D.equivExpression e1 e2 ->
    D.nullPointerConstant e1 ->
    D.nullPointerConstant e2.
Proof.
  apply (
    expression_nrect
      (fun x => forall (y : expression' A2) (Hequiv : D.equivExpression' x y) (Hnull1 : D.nullPointerConstant' x), D.nullPointerConstant' y)
      (fun x => forall y (Hequiv : D.equivExpression x y) (Hnull1 : D.nullPointerConstant x), D.nullPointerConstant y)
      (fun _ => True)
  ); intros;
  first [inversion Hequiv; subst | now trivial];
  inversion Hnull1; subst;
  constructor; solve [assumption | apply H; assumption].
Qed.
