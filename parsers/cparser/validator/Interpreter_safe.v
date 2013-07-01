(*
LR(1) parser validator
Copyright (C) 2011 INRIA

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>

Jacques-Henri Jourdan <jacques-henri.jourdan@ens.fr>
*)

Require Import Streams.
Require Import List.
Require Import Syntax.
Require Import Alphabet.
Require Grammar.
Require Automaton.
Require Validator_safe.
Require Interpreter.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).
Module Import Valid := Validator_safe.Make A.

(** * A correct automaton does not crash **)

(** We prove that a correct automaton won't crash : the interpreter will
    not return [Err] **)

(** The stack of symbols of an automaton stack **)
Fixpoint symb_stack_of_stack (stack:stack) :=
  match stack with
    | Nil_stack =>
      []
    | Cons_stack s _ q =>
      last_symb_of_non_init_state s::symb_stack_of_stack q
  end.

(** The stack of states of an automaton stack **)
Fixpoint state_stack_of_stack (stack:stack) :=
  match stack with
    | Nil_stack =>
      [singleton_state_pred Init]
    | Cons_stack s _ q =>
      singleton_state_pred s::state_stack_of_stack q
  end.

(** The stack invariant : it basically states that the assumptions on the
    states are true. **)
Inductive stack_invariant: stack -> Prop :=
  | stack_invariant_constr:
    forall stack,
      prefix      (head_symbs_of_state (state_of_stack stack))
                  (symb_stack_of_stack stack) ->
      prefix_pred (head_states_of_state (state_of_stack stack))
                  (state_stack_of_stack stack) ->
      stack_invariant_rec stack ->
      stack_invariant stack
with stack_invariant_rec: stack -> Prop :=
  | stack_invariant_rec_nil:
      stack_invariant_rec Nil_stack
  | stack_invariant_rec_cons:
    forall state_cur st stack_rec,
      stack_invariant stack_rec ->
      stack_invariant_rec (Cons_stack state_cur st stack_rec).

(** [pop] conserves the stack invariant and does not crash
     under the assumption that we can pop at this place.
     Moreover, after a pop, the top state of the stack is allowed. **)
Lemma pop_stack_invariant_conserved
  (symbols_to_pop:list symbol) (stack_cur:stack)
  (symbols_popped:list symbol) sem_popped:
  stack_invariant stack_cur ->
  prefix symbols_to_pop (head_symbs_of_state (state_of_stack stack_cur)) ->
  match pop symbols_to_pop stack_cur symbols_popped sem_popped with
    | OK (stack_new, _) =>
      stack_invariant stack_new /\
      state_valid_after_pop
        (state_of_stack stack_new) symbols_to_pop
        (head_states_of_state (state_of_stack stack_cur))
    | Err => False
  end.
Proof.
intros.
assert (stack_invariant stack_cur).
now assumption.
destruct H.
revert H H0 H1 H2 H3.
generalize (head_symbs_of_state (state_of_stack stack0)).
generalize (head_states_of_state (state_of_stack stack0)).
revert stack0 symbols_popped sem_popped.
induction symbols_to_pop; intros.
simpl.
split.
now exact H1.
destruct l.
now apply (state_valid_after_pop_nil2 (state_of_stack stack0)).
apply (state_valid_after_pop_nil1 (state_of_stack stack0)).
inversion H2.
assert (implb (f2 (state_of_stack stack0)) (b (state_of_stack stack0)) = true).
now apply H7.
destruct (f2 (state_of_stack stack0)) as [] _eqn.
now exact H9.
destruct stack0; simpl in *.
inversion H6.
rewrite H11 in Heqb0.
unfold singleton_state_pred in Heqb0.
now rewrite compare_refl in Heqb0; discriminate.
inversion H6.
rewrite H11 in Heqb0.
unfold singleton_state_pred in Heqb0.
now rewrite compare_refl in Heqb0; discriminate.
destruct stack0; unfold pop.
inversion H0.
rewrite <- H5 in H.
now inversion H.
fold pop.
destruct (compare_eqdec (last_symb_of_non_init_state state_cur) a).
inversion H0.
rewrite <- H5 in H.
inversion H.
inversion H3.
rewrite <- e in *.
unfold eq_rect.
assert (prefix_pred (List.tl l) (state_stack_of_stack stack0)).
unfold tl.
destruct l.
apply prefix_pred_nil.
now inversion H2; assumption.
assert (stack_invariant_rec stack0).
now inversion H14; assumption.
specialize (IHsymbols_to_pop stack0 (_::_) (s, sem_popped) _ _ H9 H7 H14 H17 H18).
revert IHsymbols_to_pop.
generalize (pop symbols_to_pop stack0 (_::_) (s, sem_popped)).
destruct r.
exact id.
destruct p.
intuition.
destruct l; simpl in H20.
now apply (state_valid_after_pop_nil2 (state_of_stack s0)).
apply (state_valid_after_pop_cons (state_of_stack s0)).
now assumption.
inversion H0.
rewrite <- H5 in H.
inversion H.
apply n.
now trivial.
Qed.

(** [prefix] is associative **)
Lemma prefix_ass:
  forall (l1 l2 l3:list symbol), prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
Proof.
induction l1; intros.
now apply prefix_nil.
inversion H.
rewrite <- H2 in H0.
inversion H0.
apply prefix_cons.
apply (IHl1 l4); assumption.
Qed.

(** [prefix_pred] is associative **)
Lemma prefix_pred_ass:
  forall (l1 l2 l3:list (state->bool)),
  prefix_pred l1 l2 -> prefix_pred l2 l3 -> prefix_pred l1 l3.
Proof.
induction l1; intros.
now apply prefix_pred_nil.
inversion H.
rewrite <- H4 in H0.
inversion H0.
apply prefix_pred_cons.
intro.
specialize (H3 x).
specialize (H8 x).
destruct (f3 x); simpl in *; intuition.
rewrite H8 in H3; intuition.
now apply (IHl1 l4); assumption.
Qed.

(** If the automaton is safe and we have the right to reduce at this state,
    then the stack invariant is conserved by [reduce] and [reduce]
    does not crash. **)
Lemma reduce_stack_invariant_conserved
    (stack:stack) (prod:production):
  stack_invariant stack ->
  safe ->
  valid_for_reduce (state_of_stack stack) prod ->
  match reduce stack prod with
    | OK stack_new => stack_invariant stack_new
    | Err => False
  end.
Proof.
unfold safe, valid_for_reduce.
intuition.
unfold reduce.
pose proof (pop_stack_invariant_conserved (rev (prod_rhs prod)) stack [] ()).
destruct (pop (rev (prod_rhs prod)) stack [] ()).
now apply H9; assumption.
destruct p.
destruct (H9 H H0).
specialize (H6 (state_of_stack s) (prod_lhs prod)).
specialize (H8 (state_of_stack s) (prod_lhs prod)).
intros.
unfold bind2.
destruct (goto_table (state_of_stack s) (prod_lhs prod)) as [] _eqn.
destruct s0.
apply stack_invariant_constr.
unfold symb_stack_of_stack, state_of_stack, head_symbs_of_state.
apply prefix_cons.
eapply prefix_ass.
now apply H6.
destruct H11.
now assumption.
apply prefix_pred_cons.
intro.
simpl.
now destruct (singleton_state_pred x x0); reflexivity.
eapply prefix_pred_ass.
now apply H8.
destruct H11.
now assumption.
apply stack_invariant_rec_cons.
now exact H11.
intros.
now exact (H4 _ H12 Heqo).
Qed.

(** If the automaton is safe, then the stack invariant is conserved by
    [step] and [step] does not crash. **)
Lemma step_stack_invariant_conserved (stack:stack) buffer:
  safe ->
  stack_invariant stack ->
  match step stack buffer with
    | OK (Fail_sr | Accept_sr _ _) => True
    | OK (Progress_sr stack_new _) => stack_invariant stack_new
    | Err => False
  end.
Proof.
intro.
pose proof H.
unfold safe in H.
intuition.
unfold step.
specialize (H4 (state_of_stack stack)).
specialize (H6 (state_of_stack stack)).
specialize (H9 (state_of_stack stack)).
unfold initial_no_accept in H2.
destruct (action_table (state_of_stack stack)) as [] _eqn.
destruct d.
assert (valid_for_reduce (state_of_stack stack) p).
now assumption.
pose proof (reduce_stack_invariant_conserved stack p H1 H0 H8).
destruct (reduce stack p).
now destruct H10.
now exact H10.
destruct stack.
simpl in Heqs.
rewrite Heqs in H2.
assumption.
destruct stack0.
destruct (compare_eqdec (last_symb_of_non_init_state state_cur) start_symbol).
unfold accept_initial in H3.
now exact I.
now exact (n (H _ Heqs)).
specialize (H3 state_cur).
simpl in Heqs.
rewrite Heqs in H3.
inversion H1.
inversion H10.
destruct (past_state_of_non_init_state state_cur).
now exact H3.
destruct l.
inversion H18.
specialize (H22 state_cur0).
unfold singleton_state_pred in H22.
rewrite compare_refl in H22.
now discriminate (H3 state_cur0 H22).
now exact H3.
destruct buffer.
destruct t.
specialize (H4 x).
specialize (H6 x).
specialize (H9 x).
unfold Streams.hd.
destruct (a x).
apply stack_invariant_constr.
unfold state_of_stack, symb_stack_of_stack.
apply prefix_cons.
eapply prefix_ass.
now apply H4.
destruct H1.
now assumption.
apply prefix_pred_cons.
intro.
simpl.
now destruct (singleton_state_pred s0 x0); reflexivity.
eapply prefix_pred_ass.
now apply H6.
destruct H1.
now assumption.
apply stack_invariant_rec_cons.
now assumption.
assert (valid_for_reduce (state_of_stack stack) p).
assumption.
pose proof (reduce_stack_invariant_conserved stack p H1 H0 H9).
destruct (reduce stack p).
now destruct H10.
now exact H10.
now exact I.
Qed.

(** If the automaton is safe, then it does not crash **)
Theorem parse_no_err buffer n_steps:
  safe ->
  parse buffer n_steps <> Err.
Proof.
intro.
unfold parse.
assert (stack_invariant Nil_stack).
apply stack_invariant_constr.
unfold state_of_stack, symb_stack_of_stack, head_symbs_of_state.
now apply prefix_nil.
unfold head_states_of_state.
unfold past_state_of_state.
apply prefix_pred_cons.
intro.
unfold state_of_stack.
now destruct (singleton_state_pred Init x); reflexivity.
simpl.
now apply (prefix_pred_nil []).
now apply stack_invariant_rec_nil.
revert H0.
generalize buffer Nil_stack.
induction n_steps; simpl.
now discriminate.
intros.
pose proof (step_stack_invariant_conserved s buffer0 H H0).
destruct (step s buffer0); simpl.
now destruct H1.
destruct s0; try discriminate.
apply IHn_steps.
now assumption.
Qed.

(** A version of [parse] that uses safeness in order to return a
   [parse_result], and not a [result parse_result] : we have proven that
   parsing does not return [Err]. **)
Definition parse_with_safe (safe:safe) (buffer:Stream token) (n_steps:nat):
  parse_result.
Proof.
destruct (parse buffer n_steps) as [] _eqn.
now destruct (parse_no_err buffer n_steps safe Heqr).
now exact p.
Defined.

End Make.
