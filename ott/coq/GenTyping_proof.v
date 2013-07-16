Require Import Common.

Require Import AilTypes.
Require Import AilSyntax.
Require Import AilTyping.
Require Import GenTypes.
Require Import GenTyping.
Require Import Annotation.

Require Import Context_proof.
Require Import AilSyntax_proof.


Module D.
Include AilSyntax_defns.
Require AilSyntaxAux_defns.
Include AilSyntaxAux_defns.
Require AilTyping_defns.
Include AilTyping_defns.
End D.

Require Tactics.

Ltac annotate_expression_equiv_tac_inner c :=
  match c with
  | _                        =>
      is_var c; destruct c; try congruence
  | match ?c with _ => _ end =>
      annotate_expression_equiv_tac_inner c
  | annotate_expression ?A ?S ?G ?e => match goal with IH : forall _, annotate_expression A S G e = _ -> _ |- _ =>
                                         let y := fresh in
                                         destruct (annotate_expression A S G e) as [y|];
                                         [pose proof (IH y eq_refl)|congruence]
                                       end
  | annotate_arguments ?A ?S ?G ?es ?p => match goal with IH : forall _ _, annotate_arguments A S G _ _ = _ -> _ |- _ =>
                                         let Heq := fresh in
                                         let y := fresh in
                                         case_eq (annotate_arguments A S G es p);
                                         [intros y Heq; pose proof (IH y p Heq); clear Heq|congruence]
                                       end
  | annotate_expression' ?A ?S ?G ?e => match goal with IH : forall _ _, annotate_expression' A S G e = _ -> _ |- _ =>
                                          let y := fresh in
                                          destruct (annotate_expression' A S G e) as [[y gt]|];
                                          [pose proof (IH y gt eq_refl)|congruence]
                                       end
  | _ => destruct c; try congruence
  end.

Ltac annotate_expression_equiv_tac :=
  match goal with
  | [|- ((match ?c with _ => _ end) = _) -> _] =>
      annotate_expression_equiv_tac_inner c
  end.

Lemma annotate_expression_equiv {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e} {e'} :
  annotate_expression A S G e = Some e' ->
  D.equivExpression e e'.
Proof.
  apply (
    expression_nrect
      (fun x => forall y gt (Heq : annotate_expression' A S G x = Some (y, gt)), D.equivExpression' x y)
      (fun x => forall y (Heq : annotate_expression A S G x = Some y), D.equivExpression x y)
      (fun x => forall y p (Heq : annotate_arguments A S G x p = Some y), D.equivArguments x y)
  ); intros; revert Heq; simpl;
  fold (@annotate_rvalue A1 A2 B1 B2 A S G);
  fold (@annotate_assignee A1 A2 B1 B2 A S G);
  fold (@annotate_arguments A1 A2 B1 B2 A S G);
  unfold annotate_assignee;
  unfold annotate_assignee_aux;
  unfold annotate_rvalue;
  unfold annotate_rvalue_aux;
  unfold option_bind;
  repeat annotate_expression_equiv_tac;
  intros; Tactics.subst_no_fail; Tactics.autoinjections;
  constructor; assumption.
Qed.

Lemma annotate_rvalue_equiv {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {e} {e'} {gt} :
  annotate_rvalue A S G e = Some (e', gt) ->
  D.equivExpression e e'.
Proof.
  unfold annotate_rvalue.
  unfold annotate_rvalue_aux.
  unfold option_bind.
  case_eq (annotate_expression A S G e); [|congruence].
  intros ? Heq; pose proof (annotate_expression_equiv Heq).
  my_auto.
Qed.

Ltac match_destruct_inner d :=
  match d with
  | match ?d with _ => _ end => match_destruct_inner d
  | _ => destruct d
  end.

Ltac match_destruct :=
  match goal with
  | |- context[match ?d with _ => _ end] => match_destruct_inner d
  end.

Lemma annotate_assignee_equiv {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {t} {e} {e'} :
  annotate_assignee A S G t e = Some e' ->
  D.equivExpression e e'.
Proof.
  unfold annotate_assignee.
  unfold annotate_assignee_aux.
  unfold option_bind.
  case_eq (annotate_rvalue A S G e); [|congruence].
  intros [? ?] Heq; pose proof (annotate_rvalue_equiv Heq).
  match_destruct; my_auto.
Qed.

Lemma annotate_definitions_equiv {A1 A2 B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G} {ds} {ds'} :
  annotate_definitions A S G ds = Some ds' ->
  D.equivDeclaration ds ds'.
Proof.
  intros Heq.
  revert ds' Heq.
  induction ds as [|[? ?]]; intros; revert Heq; simpl.
  - injection 1; intros; my_auto.
  - unfold annotate_definition.
    unfold option_bind.
    match_destruct; [|congruence].
    destruct p as [_ t].
    case_eq (annotate_assignee A S G t e); [|congruence].
    intros ? Heq; pose proof (annotate_assignee_equiv Heq); clear Heq.
    case_eq (annotate_definitions A S G ds); [|congruence].
    intros ? Heq; pose proof (IHds _ Heq); clear Heq.
    injection 1; intros; my_auto.
Qed.

Ltac annotate_statement_equiv_tac_inner c :=
  match c with
  | _                        =>
      is_var c; destruct c; try congruence
  | match ?c with _ => _ end =>
      annotate_statement_equiv_tac_inner c
  | annotate_expression ?A ?S ?G ?e => let Heq := fresh in
                                       case_eq (annotate_expression A S G e); [|congruence];
                                       intros ? Heq; pose proof (annotate_expression_equiv Heq); clear Heq
  | annotate_rvalue ?A ?S ?G ?e => let Heq := fresh in
                                       case_eq (annotate_rvalue A S G e); [|congruence];
                                       intros [? ?] Heq; pose proof (annotate_rvalue_equiv Heq); clear Heq
  | annotate_assignee ?A ?S ?G ?t ?e => let Heq := fresh in
                                        case_eq (annotate_assignee A S G t e); [|congruence];
                                        intros ? Heq; pose proof (annotate_assignee_equiv Heq); clear Heq
  | annotate_definitions ?A ?S ?G ?ds => let Heq := fresh in
                                       case_eq (annotate_definitions A S G ds); [|congruence];
                                       intros ? Heq; pose proof (annotate_definitions_equiv Heq); clear Heq
  | annotate_statement ?A ?S ?G ?t ?s => match goal with IH : forall _ _, annotate_statement A S _ t s = _ -> _ |- _ =>
                                           let Heq := fresh in
                                           case_eq (annotate_statement A S G t s);
                                           [intros ? Heq; pose proof (IH _ G Heq); clear Heq|congruence]
                                       end
  | annotate_statement' ?A ?S ?G ?t ?s => match goal with IH : forall _ _, annotate_statement' A S _ t s = _ -> _ |- _ =>
                                         let Heq := fresh in
                                         case_eq (annotate_statement' A S G t s);
                                         [intros ? Heq; pose proof (IH _ G Heq); clear Heq|congruence]
                                       end
  | annotate_block ?A ?S ?G ?t ?ss => match goal with IH : forall _ _, annotate_block A S _ t ss = _ -> _ |- _ =>
                                         let Heq := fresh in
                                         case_eq (annotate_block A S G t ss);
                                         [intros ? Heq; pose proof (IH _ G Heq); clear Heq|congruence]
                                       end
  | _ => destruct c; try congruence
  end.

Ltac annotate_statement_equiv_tac :=
  match goal with
  | [|- ((match ?c with _ => _ end) = _) -> _] =>
      annotate_statement_equiv_tac_inner c
  end.

Lemma annotate_statement_equiv {A1 A2 B  B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} {G : gamma} {t_return} {s : statement B A1} {s' : statement B A2} :
  annotate_statement A S G t_return s = Some s' ->
  D.equivStatement s s'.
Proof.
  revert s s' G.
  apply (
    statement_nrect
      (fun x => forall y G (Heq : annotate_statement' A S G t_return x = Some y), D.equivStatement' x y)
      (fun x => forall y G (Heq : annotate_statement A S G t_return x = Some y), D.equivStatement x y)
      (fun x => forall y G (Heq : annotate_block A S G t_return x = Some y), D.equivBlock x y)
  ); intros; revert Heq; simpl;
  unfold option_bind;
  unfold andb;
  unfold orb;
  repeat match goal with
  | |- context [annotate_block_aux A (annotate_statement A S ?G ?t_return) ?ss] => fold (annotate_block A S G t_return ss)
  end;
  repeat annotate_statement_equiv_tac;
  intros; Tactics.subst_no_fail; Tactics.autoinjections;
  constructor; assumption.
Qed.

Lemma annotate_function_equiv {A1 A2 B B1 B2 : Set} {A : annotation A1 A2} {S : sigma B1 B2} :
  forall {p : _ * _ * statement B A1} {p' : _ * _ * statement B A2},
    annotate_function A S p = Some p' ->
    cross2 eq (@D.equivStatement B B A1 A2) p p'.
Proof.
  intros [[? ?] ?] [[? ?] ?].
  unfold annotate_function.
  unfold option_bind.
  match_destruct; [|congruence].
  match goal with
  | |- context[annotate_statement ?A ?S ?G ?t ?s] =>
      let Heq := fresh in
      case_eq (annotate_statement A S G t s); [|congruence];
      intros ? Heq; pose proof (annotate_statement_equiv Heq); clear Heq
  end;
  intros; Tactics.subst_no_fail; Tactics.autoinjections; now my_auto.
Qed.

Lemma annotate_sigma_equiv {A1 A2 B : Set} {A : annotation A1 A2} {S : sigma B A1} {S' : sigma B A2} :
  annotate_sigma A S = Some S' ->
  D.equivSigma S S'.
Proof.
  intros Heq.
  exact (mapP_sound eq_identifier_correct (fun p1 p2 => annotate_function_equiv (A:=A) (B:=B) (S:=S) (p:=p1) (p':=p2)) Heq).
Qed.

Lemma annotate_program_equiv {A1 A2 B : Set} {A : annotation A1 A2} :
  forall {p : program B A1} {p' : program B A2},
    annotate_program A p = Some p' ->
    D.equivProgram p p'.
Proof.
  intros [m S] [m' S'].
  unfold annotate_program.
  unfold option_bind.
  case_eq (annotate_sigma A S).
  - intros ? Heq; pose proof (annotate_sigma_equiv Heq); clear Heq;
    my_auto; inversion 1; subst; constructor; finish assumption.
  - my_auto.
Qed.
