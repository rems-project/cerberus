Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.
Require Import GenTypes.

Require Import AilTypes_proof.
Require Import AilSyntax_proof.

Lemma eq_genIntegerType_correct :
  forall x y, boolSpec (eq_genIntegerType x y) (x = y).
Proof.
  induction x; destruct y; simpl;
  unfold boolSpec; unfold andb;
  repeat match goal with
  | |- eq_integerType ?x ?y = _ -> _ => case_fun (eq_integerType_correct x y)
  | |- eq_integerConstant ?x ?y = _ -> _ => case_fun (eq_integerConstant_correct x y)
  | IH : forall _, boolSpec _ (?x = _) |- eq_genIntegerType ?x ?y = _ -> _ => case_fun (IH y)
  | _ => context_destruct
  end; solve [congruence|discriminate].
Qed.

Lemma eq_genBasicType_correct x y :
  boolSpec (eq_genBasicType x y) (x = y).
Proof.
  destruct x, y; simpl.
  match goal with
  | |- boolSpec (_ ?x ?y) _ => pose proof (eq_genIntegerType_correct x y); boolSpec_destruct
  end; solve [congruence|discriminate].
Qed.

Lemma eq_genType_correct :
  forall x y, boolSpec (eq_genType x y) (x = y).
Proof.
  induction x;
  destruct y; simpl;
  unfold boolSpec;
  unfold andb;
  repeat match goal with
  | |- eq_genBasicType  ?x ?y = _ -> _ => case_fun (eq_genBasicType_correct  x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_nat        ?x ?y = _ -> _ => case_fun (eq_nat_correct x y)
  | H : forall _, boolSpec (eq_genType  ?x _) _ |- eq_genType  ?x ?y = _ -> _=> case_fun (H y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- eq_params ?x ?y = _ -> _ => case_fun (eq_params_correct x y)
  | _ => context_destruct
  end; congruence.
Qed.

Lemma eq_genTypeCategory_correct x y :
  boolSpec (eq_genTypeCategory x y) (x = y).
Proof.
  destruct x, y; simpl;
  unfold boolSpec;
  unfold andb;
  repeat match goal with
  | |- eq_genType ?x ?y = _ -> _ => case_fun (eq_genType_correct x y)
  | |- eq_qualifiers ?x ?y = _ -> _ => case_fun (eq_qualifiers_correct x y)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | _ => context_destruct
  end; congruence.
Qed.
