Require Import Common.
Require Import AilTypes AilTypes_proof.
Require Import AilTypesAux AilTypesAux_proof.
Require Import AilWf.

Require AilWf_defns.
Module D := AilWf_defns.

Lemma adjusted_correct t :
  boolSpec (adjusted t) (D.adjusted t).
Proof.
  do 2 unfold_goal.
  unfold andb.
  unfold negb.
  set (array_correct t).
  set (function_correct t).
  repeat boolSpec_destruct; my_auto.
Qed.

Lemma wfLvalue_incl {q} {t} :
  D.wfLvalue q t -> D.wfType t.
Proof.
  destruct t;
  inversion 1;
  finish ltac:(now
    match goal with
    | [H : ~ D.pointer  (Pointer _ _) |- _] => exfalso; apply H; constructor
    | [H :   D.function (Array   _ _) |- _] => inversion H
    end
  ).
Qed.

Ltac function_neg :=
  match goal with
  | [H :   D.function Void           |- _] => inversion H
  | [H :   D.function (Basic      _) |- _] => inversion H
  | [H :   D.function (Array    _ _) |- _] => inversion H
  | [H :   D.function (Pointer  _ _) |- _] => inversion H
  | [H : ~ D.function (Function _ _) |- _] => exfalso; apply H; constructor
  end.

Lemma wf_lvalue_aux_correct q t :
  D.wfType t -> 
  boolSpec (wf_lvalue_aux q t) (D.wfLvalue q t).
Proof.
  intros.
  do 2 unfold_goal.
  unfold negb.
  unfold implb.
  repeat match goal with
  | |- function      ?x = _ -> _ => case_fun (function_correct      x)
  | |- object        ?x = _ -> _ => case_fun (object_correct        x)
  | |- array         ?x = _ -> _ => case_fun (array_correct         x)
  | |- unqualified   ?x = _ -> _ => case_fun (unqualified_correct   x)
  | |- restrict      _ = ?b -> _ => destruct b; [|rewrite <- Bool.not_true_iff_false]; intros ?
  | _ => function_neg
  | _ => context_destruct
  end; solve [econstructor (now my_auto) | inversion 1; my_auto].
Qed.

Lemma wf_type_correct :
  forall x, boolSpec (wf_type x) (D.wfType x).
Proof.
  apply (ctype_nrect
           (fun x => boolSpec (wf_type       x) (D.wfType       x))
           (fun x => boolSpec (wf_parameters x) (D.wfParameters x)));
  intros; simpl;
  unfold boolSpec;
  fold wf_parameters;
  unfold andb; unfold negb;
  repeat match goal with
  | |- wf_type       ?x = _ -> _ => case_fun (wf_type_correct       x)
  | |- wf_parameters ?x = _ -> _ => case_fun (wf_parameters_correct x)
  | |- incomplete    ?x = _ -> _ => case_fun (incomplete_correct    x)
  | |- adjusted      ?x = _ -> _ => case_fun (adjusted_correct      x)
  | |- complete      ?x = _ -> _ => case_fun (complete_correct      x)
  | |- array         ?x = _ -> _ => case_fun (array_correct         x)
  | |- function      ?x = _ -> _ => case_fun (function_correct      x)
  | |- object        ?x = _ -> _ => case_fun (object_correct        x)
  | |- unqualified   ?x = _ -> _ => case_fun (unqualified_correct   x)
  | |- restrict      _ = ?b -> _ => destruct b; [|rewrite <- Bool.not_true_iff_false]; intros ?
  | H : D.wfType ?t |- wf_lvalue_aux ?q ?t = _ -> _ => case_fun (wf_lvalue_aux_correct q t H)
  | |- D.wfType       _   => econstructor (eassumption)
  | |- D.wfParameters _   => econstructor (eassumption)
  | |- D.wfLvalue     _ _ => econstructor (finish eassumption)
  | Hfalse : ~ D.wfType ?t, H : D.wfLvalue _ ?t |- False => exact (Hfalse (wfLvalue_incl H))
  | |- ~ _ => inversion 1; subst; try finish ltac:(now function_neg)
  | _ => boolSpec_simpl; try context_destruct
  end.
Qed.

Lemma wf_lvalue_correct q t :
  boolSpec (wf_lvalue q t) (D.wfLvalue q t).
Proof.
  do 2 unfold_goal; unfold andb.
  set (wf_type_correct t) as H     ; boolSpec_destruct; [|my_auto].
  set (wf_lvalue_aux_correct q t H); boolSpec_destruct; my_auto.
Qed.
