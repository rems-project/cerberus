Require Import Common.
Require Import Context.
Require Import AilTypes.
Require Import AilSyntax.
Require Import AilTypesAux.
Require Import AilTyping.
Require Import AilTypingStatements.

Require Import Context_proof.
Require Import AilTypes_proof.
Require Import AilSyntax_proof.
Require Import AilTypesAux_proof.
Require Import AilWf_proof.
Require Import AilTyping_proof.

Module D.
  Require AilTypingStatements_defns.

  Include Context_defns.
  Include AilTyping_defns.
  Include AilTypingStatements_defns.
End D.

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

Lemma well_typed_block_correct_aux {A B} P G (S : sigma A B) t_return :
  (forall  s, boolSpec (well_typed_statement P G S t_return s) (D.wellTypedStatement P G S t_return s)) ->
  (forall ss, boolSpec (well_typed_block P G S t_return ss) (allList (D.wellTypedStatement P G S t_return) ss)).
Proof.
  intros well_typed_statement_correct.
  induction ss; simpl;
  unfold boolSpec;
  unfold andb;
  repeat match goal with
  | |- well_typed_statement P G S t_return ?s = _ -> _ => case_fun (well_typed_statement_correct s)
  | |- well_typed_block P G S t_return ?ss = _ -> _ => case_fun IHss
  | _ => context_destruct
  | |- allList _ _ => constructor; assumption
  | |- neg _ =>  inversion_clear 1; contradiction
  end.
Qed.

Lemma well_typed_definition_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall d, boolSpec (well_typed_definition P G S d) (D.wellTypedDefinition P G S d).
Proof.
  intros Hdisjoint d.
  do 2 unfold_goal.
  repeat match goal with
  | |- lookup G ?v = _ -> _ => case_fun (lookup_correct G v)
  | |- assignable P G S ?t ?e = _ -> _ => case_fun (assignable_correct P G S Hdisjoint t e)
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

Lemma well_typed_definitions_correct {A B} P G (S : sigma A B) :
  D.disjoint G S ->
  forall ds, boolSpec (well_typed_definitions P G S ds) (allList (D.wellTypedDefinition P G S) ds).
Proof.
  intros Hdisjoint.
  apply all_list_correct.
  apply well_typed_definition_correct.
  assumption.
Qed.

Lemma well_typed_statement_correct {A B} P (S : sigma A B) t_return :
  forall s G (Hdisjoint : D.disjoint G S),
  boolSpec (well_typed_statement P G S t_return s) (D.wellTypedStatement P G S t_return s).
Proof.
  eapply (
    statement_nrect
      (fun s  => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_statement' P G S t_return s ) (D.wellTypedStatement' P G S t_return s))
      (fun s  => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_statement  P G S t_return s ) (D.wellTypedStatement P G S t_return s))
      (fun ss => forall G (Hdisjoint : D.disjoint G S), boolSpec (well_typed_block      P G S t_return ss) (allList (D.wellTypedStatement P G S t_return) ss))
  );
  intros; simpl;
  match goal with
  | |- context [well_typed_block_aux (well_typed_statement _ ?G _ _) ?ss] => fold (@well_typed_block A B P G S t_return ss)
  | _ => idtac
  end;
  unfold boolSpec; unfold andb;
  repeat match goal with
  | |- fresh_bindings ?bs ?C = _ -> _ => case_fun (fresh_bindings_correct C bs)
  | |- typeable _ ?G _ ?e = _ -> _ => case_fun (typeable_correct P G S Hdisjoint e)
  | |- assignable _ ?G _ ?t1 ?e2 = _ -> _ => case_fun (assignable_correct P G S Hdisjoint t1 e2)
  | |- type_of_rvalue _ ?G _ ?e = _ -> _ => case_fun (type_of_rvalue_correct P G S Hdisjoint e)
  | |- scalar ?t = _ -> _ => case_fun (scalar_correct t)
  | |- integer ?t = _ -> _ => case_fun (integer_correct t)
  | |- eq_ctype ?x ?y = _ -> _ => case_fun (eq_ctype_correct x y)
  | |- type_of_constant _ ?ic = _ -> _ => case_fun (type_of_constant_correct P ic)
  | |- well_typed_definitions _ ?G _ ?ds = _ -> _ => case_fun (well_typed_definitions_correct P G S Hdisjoint ds)
  | |- well_formed_bindings ?bs = _ -> _ => case_fun (well_formed_bindings_correct bs)
  | IH : forall _ _, boolSpec _ (D.wellTypedStatement  _ _ _ _ ?s) |- well_typed_statement  _ ?G _ _ ?s = _ -> _ => case_fun (IH G Hdisjoint)
  | IH : forall _ _, boolSpec _ (D.wellTypedStatement' _ _ _ _ ?s) |- well_typed_statement' _ ?G _ _ ?s = _ -> _ => case_fun (IH G Hdisjoint)
  | IH : forall _ _, boolSpec _ (allList (D.wellTypedStatement _ _ _ _) ?ss) |- well_typed_block _ ?G _ _ ?ss = _ -> _ =>
      is_var G; case_fun (IH _ Hdisjoint)
  | H : D.wellFormedBindings _, IH : forall _ _, boolSpec _ (allList (D.wellTypedStatement _ _ _ _) ?ss) |-well_typed_block _ ?G _ _ ?ss = _ -> _ =>
      not_var G;
      let IH' := fresh in
      assert (boolSpec (well_typed_block P G S t_return ss) (allList (D.wellTypedStatement P G S t_return) ss))
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
  | H1 : D.typeOfRValue P _ S ?e ?t1
  , H2 : D.typeOfRValue P _ S ?e ?t2 |- _ => notSame t1 t2; pose proof (typeOfRValue_functional Hdisjoint _ H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  | H1 : neg ?P, H2 : ?P |- False => destruct (H1 H2)
  | H1 : forall _, neg (?P _), H2 : ?P _ |- False => destruct (H1 _ H2)
  | H :  neg (?c = ?c) |- False => apply H; constructor
  end.
Qed.

Lemma well_typed_function_correct {A B : Set} P (S : sigma A B) p :
  boolSpec (well_typed_function P S p) (D.wellTypedFunction P S p).
Proof.
  do 2 unfold_goal.
  unfold andb.
  repeat match goal with
  | |- fresh_bindings ?bs ?S = _ -> _ => case_fun (fresh_bindings_correct S bs)
  | |- well_formed_bindings ?bs = _ -> _ => case_fun (well_formed_bindings_correct bs)
  | |- AilWf.wf_type ?t = _ -> _ => case_fun (wf_type_correct t)
  | H : D.wellFormedBindings ?bs |- well_typed_statement _ (add_bindings ?bs nil) _ ?t ?s = _ -> _ =>
      notHyp (D.disjoint (add_bindings b nil) S);
      let Hdisjoint := fresh in
      assert (D.disjoint (add_bindings b nil) S) as Hdisjoint
        by (
          apply disjoint_freshBindings; [
              inversion_clear H; assumption
            | assumption
            | intros ? [? Hfalse]; inversion Hfalse
          ]
        );
      case_fun (well_typed_statement_correct P S t s (add_bindings bs nil) Hdisjoint)
  | _ => context_destruct
  | |- D.wellTypedFunction _ _ _ =>  constructor; assumption
  | |- neg _ => now (inversion 1; my_auto)
  end.
Qed.

Definition well_typed_sigma_correct {A B : Set} P (S : sigma A B) :
  boolSpec (well_typed_sigma P S) (D.wellTypedSigma P S).
Proof.
  do 2 unfold_goal.
  match goal with
  | |- if ?t then _ else _ =>
      pose proof (all_correct eq_identifier_correct (fun _ => well_typed_function_correct P S) S : boolSpec t _);
      boolSpec_destruct
  end; my_auto.
Qed.

Lemma well_typed_program_correct {A B} P (p : _ * sigma A B) :
  boolSpec (well_typed_program P p) (D.wellTypedProgram P p).
Proof.
  do 2 unfold_goal.
  repeat match goal with
  | |- lookup ?S ?v = _ -> _ => case_fun (lookup_correct S v)
  | |- well_typed_sigma ?P ?S = _ -> _ => case_fun (well_typed_sigma_correct P S)
  | _ => context_destruct
  | |- D.wellTypedProgram _ _ => econstructor; eassumption
  end;
  inversion_clear 1;
  repeat match goal with
  | H1 : D.lookup ?S ?id ?t1, H2 : D.lookup ?S ?id ?t2 |- _ => pose proof (lookup_functional H1 H2); Tactics.subst_no_fail; Tactics.autoinjections; clear H1
  end; my_auto; firstorder.
Qed.

