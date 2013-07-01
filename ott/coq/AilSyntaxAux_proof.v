Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux.
Require Import AilTypesAux_fun.
Require Import AilTypesAux_proof.
Require Import AilSyntax.
Require Import AilSyntaxAux. 
Require Import AilSyntaxAux_fun.

Fixpoint fv_fun_correct           id e : boolSpec (fv_fun           id e) (fv           id e)
with     fv_arguments_fun_correct id l : boolSpec (fv_arguments_fun id l) (fv_arguments id l).
Proof.
  + unfold_goal.
    destruct e;
    try set (fv_fun_correct id e );
    try set (fv_fun_correct id e1);
    try set (fv_fun_correct id e2);
    try set (fv_fun_correct id e3);
    try set (fv_arguments_fun_correct id l);
    my_auto' fail ltac:(progress (bool_simpl; boolSpec_simpl)).
  + unfold_goal.
    destruct l;
    try set (fv_fun_correct id e);
    try set (fv_arguments_fun_correct id l);
    my_auto' fail ltac:(progress (bool_simpl; boolSpec_simpl)).
Defined.

Ltac isNullPointerConstant_fun_tac :=
  match goal with
  | [|- boolSpec (isNullPointerConstant_fun ?e) _] =>
      is_var e; unfold boolSpec; destruct e; simpl; try finish fail; repeat var_destruct
  end.

Fixpoint isNullPointerConstant_fun_correct e : boolSpec (isNullPointerConstant_fun e) (isNullPointerConstant e).
Proof.
  unfold_goal.
  destruct e; simpl;
  unfold andb;
  repeat match goal with
  | [|- isNullPointerConstant_fun ?e = _ -> _] => case_fun (isNullPointerConstant_fun_correct e)
  | [|- isUnqualified_fun ?qs        = _ -> _] => case_fun (isUnqualified_fun_correct qs)
  | _ => context_destruct
  end; try finish fail.
Defined.
