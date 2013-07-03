Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux AilTypesAux_proof.
Require Import AilSyntax AilSyntax_proof.
Require Import AilSyntaxAux.

Require AilSyntaxAux_defns.
Module D := AilSyntaxAux_defns.

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
