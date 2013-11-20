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

Require Automaton.
Require Import Alphabet.
Require Import List.
Require Import Syntax.

Module Make(Import A:Automaton.T).

(** The singleton predicate for states **)
Definition singleton_state_pred (state:state) :=
  (fun state' => match compare state state' with Eq => true |_ => false end).

(** [past_state_of_non_init_state], extended for all states. **)
Definition past_state_of_state (state:state) :=
  match state with
    | Init => []
    | Ninit nis => past_state_of_non_init_state nis
  end.

(** Concatenations of last and past **)
Definition head_symbs_of_state (state:state) :=
  match state with
    | Init => []
    | Ninit s =>
      last_symb_of_non_init_state s::past_symb_of_non_init_state s
  end.
Definition head_states_of_state (state:state) :=
  singleton_state_pred state::past_state_of_state state.

(** * Validation for correctness **)

(** The initial state do not have the accept action. That would mean nothing,
    as there is nothing on the stack for using as semantic value.
    If the user wants to recognize the empty word, then it has to reduce an
    empty production before. Note that in this case, the language shouild only
    contain the empty word, because of end of stream conflicts. **)
Definition initial_no_accept: Prop :=
  match action_table Init with
    | inl Accept_act => False
    | _ => True
  end.

Definition is_initial_no_accept: bool :=
  match action_table Init with
    | inl Accept_act => false
    | _ => true
  end.

Property is_initial_no_accept_correct:
  is_initial_no_accept = true -> initial_no_accept.
Proof.
unfold initial_no_accept, is_initial_no_accept.
destruct (action_table Init); intuition.
destruct d; intuition.
Qed.

(** If a state accepts, then the top symbol of the stack must be the start
    symbol of the grammar **)
Definition accept_last_symb :=
  forall s:noninitstate,
    action_table s = inl Accept_act ->
    last_symb_of_non_init_state s = start_symbol.

Definition is_accept_last_symb :=
  forallb (fun s:noninitstate =>
    match action_table s with
      | inl Accept_act =>
        compare_eqb (last_symb_of_non_init_state s) start_symbol
      | _ => true
    end)
    all_list.

Property is_accept_last_symb_correct:
  is_accept_last_symb = true -> accept_last_symb.
Proof.
unfold is_accept_last_symb, accept_last_symb.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
rewrite H0 in H.
apply compare_eqb_iff; intuition.
Qed.

(** If a state accepts, then the state under (in the stack) this state must be
   the initial state **)
Definition accept_initial: Prop :=
  forall s:noninitstate,
    match action_table s with
      | inl Accept_act =>
        match past_state_of_non_init_state s with
          | [p] => forall s2, p s2 = true -> s2 = Init
          | _ => False
        end
      | _ => True
    end.

Definition is_accept_initial :=
  forallb (fun s:noninitstate =>
    match action_table s with
      | inl Accept_act =>
        match past_state_of_non_init_state s with
          | [p] =>
            forallb (fun s2:state =>
              if p s2 then match s2 with Init => true | _ => false end
              else true)
              all_list
          | _ => false
        end
      | _ => true
    end)
    all_list.

Property is_accept_initial_correct:
  is_accept_initial = true -> accept_initial.
Proof.
unfold accept_initial, is_accept_initial.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s); intuition.
destruct d; intuition.
destruct (past_state_of_non_init_state s); intuition.
destruct l; intuition.
intros.
rewrite forallb_forall in H.
specialize (H s2 (all_list_forall s2)).
rewrite H0 in H.
destruct s2; intuition; discriminate.
Qed.

(** Prefix predicate between two lists of symbols. **)
Inductive prefix: list symbol -> list symbol -> Prop :=
  | prefix_nil: forall l, prefix [] l
  | prefix_cons: forall l1 l2 x, prefix l1 l2 -> prefix (x::l1) (x::l2).

Fixpoint is_prefix (l1 l2:list symbol):=
  match l1, l2 with
    | [], _ => true
    | t1::q1, t2::q2 => (compare_eqb t1 t2 && is_prefix q1 q2)%bool
    | _::_, [] => false
  end.

Property is_prefix_correct (l1 l2:list symbol):
  is_prefix l1 l2 = true -> prefix l1 l2.
Proof.
revert l2.
induction l1; intros.
apply prefix_nil.
unfold is_prefix in H.
destruct l2; intuition; try discriminate.
rewrite Bool.andb_true_iff in H.
destruct H.
rewrite compare_eqb_iff in H.
destruct H.
apply prefix_cons.
apply IHl1; intuition.
Qed.

(** If we shift, then the known top symbols of the destination state is
    a prefix of the known top symbols of the source state, with the new
    symbol added. **)
Definition shift_head_symbs :=
  forall s,
    match action_table s with
      | inr awp =>
        forall t, match awp t with
          | Shift_act s2 _ =>
            prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
          | _ => True
        end
      | _ => True
    end.

Definition is_shift_head_symbs :=
  forallb (fun s:state =>
    match action_table s with
      | inr awp =>
        forallb (fun t =>
          match awp t with
            | Shift_act s2 _ =>
              is_prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
            | _ => true
          end)
          all_list
      | _ => true
    end)
    all_list.

Property is_shift_head_symbs_correct:
  is_shift_head_symbs = true -> shift_head_symbs.
Proof.
unfold is_shift_head_symbs, shift_head_symbs.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s); intuition.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (a t); intuition.
apply is_prefix_correct; intuition.
Qed.

(** When a goto happens, then the known top symbols of the destination state
    is a prefix of the known top symbols of the source state, with the new
    symbol added. **)
Definition goto_head_symbs :=
  forall s nt,
    match goto_table s nt with
      | Some (exist s2 _) => 
        prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
      | None => True
    end.

Definition is_goto_head_symbs :=
  forallb (fun s:state =>
    forallb (fun nt =>
      match goto_table s nt with
        | Some (exist s2 _) =>
          is_prefix (past_symb_of_non_init_state s2) (head_symbs_of_state s)
        | None => true
      end)
      all_list)
    all_list.

Property is_goto_head_symbs_correct:
  is_goto_head_symbs = true -> goto_head_symbs.
Proof.
unfold is_goto_head_symbs, goto_head_symbs.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
rewrite forallb_forall in H.
specialize (H nt (all_list_forall nt)).
destruct (goto_table s nt); intuition.
destruct s0.
apply is_prefix_correct; intuition.
Qed.

(** We have to say the same kind of checks for the assumptions about the
    states stack. However, theses assumptions are predicates. So we define
    a notion of "prefix" over predicates lists, that means, basically, that
    an assumption entails another **)
Inductive prefix_pred: list (state->bool) -> list (state->bool) -> Prop :=
  | prefix_pred_nil: forall l, prefix_pred [] l
  | prefix_pred_cons: forall l1 l2 f1 f2,
     (forall x, implb (f2 x) (f1 x) = true) ->
     prefix_pred l1 l2 -> prefix_pred (f1::l1) (f2::l2).

Fixpoint is_prefix_pred (l1 l2:list (state->bool)) :=
  match l1, l2 with
    | [], _ => true
    | f1::q1, f2::q2 =>
      (forallb (fun x => implb (f2 x) (f1 x)) all_list
        && is_prefix_pred q1 q2)%bool
    | _::_, [] => false
  end.

Property is_prefix_pred_correct (l1 l2:list (state->bool)) :
  is_prefix_pred l1 l2 = true -> prefix_pred l1 l2.
Proof.
revert l2.
induction l1.
intros.
apply prefix_pred_nil.
intros.
destruct l2; intuition; try discriminate.
unfold is_prefix_pred in H.
rewrite Bool.andb_true_iff in H.
rewrite forallb_forall in H.
apply prefix_pred_cons; intuition.
apply H0.
apply all_list_forall.
Qed.

(** The assumptions about state stack is conserved when we shift **)
Definition shift_past_state :=
  forall s,
    match action_table s with
      | inr awp =>
        forall t, match awp t with
          | Shift_act s2 _ =>
            prefix_pred (past_state_of_non_init_state s2)
                        (head_states_of_state s)
          | _ => True
        end
      | _ => True
    end.

Definition is_shift_past_state:=
  forallb (fun s:state =>
    match action_table s with
      | inr awp =>
        forallb (fun t =>
          match awp t with
            | Shift_act s2 _ =>
              is_prefix_pred
                (past_state_of_non_init_state s2) (head_states_of_state s)
            | _ => true
          end)
          all_list
      | _ => true
    end)
    all_list.

Property is_shift_past_state_correct:
 is_shift_past_state = true -> shift_past_state.
Proof.
unfold is_shift_past_state, shift_past_state.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s); intuition.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (a t); intuition.
apply is_prefix_pred_correct; intuition.
Qed.

(** The assumptions about state stack is conserved when we do a goto **)
Definition goto_past_state :=
  forall s nt,
    match goto_table s nt with
      | Some (exist s2 _) =>
        prefix_pred (past_state_of_non_init_state s2)
                    (head_states_of_state s)
      | None => True
    end.

Definition is_goto_past_state :=
  forallb (fun s:state =>
    forallb (fun nt =>
      match goto_table s nt with
        | Some (exist s2 _) =>
          is_prefix_pred
            (past_state_of_non_init_state s2) (head_states_of_state s)
        | None => true
      end)
      all_list)
    all_list.

Property is_goto_past_state_correct :
  is_goto_past_state = true -> goto_past_state.
Proof.
unfold is_goto_past_state, goto_past_state.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
rewrite forallb_forall in H.
specialize (H nt (all_list_forall nt)).
destruct (goto_table s nt); intuition.
destruct s0.
apply is_prefix_pred_correct; intuition.
Qed.

(** What states are possible after having popped these symbols from the
    stack, given the annotation of the current state ? **)
Inductive state_valid_after_pop (s:state):
  list symbol -> list (state -> bool) -> Prop :=
  | state_valid_after_pop_nil1:
    forall p pl, p s = true -> state_valid_after_pop s [] (p::pl)
  | state_valid_after_pop_nil2:
    forall sl, state_valid_after_pop s sl []
  | state_valid_after_pop_cons:
    forall st sq p pl, state_valid_after_pop s sq pl ->
      state_valid_after_pop s (st::sq) (p::pl).

Fixpoint is_state_valid_after_pop
  (state:state) (to_pop:list symbol) annot :=
  match annot, to_pop with
    | [], _ => true
    | p::_, [] => p state
    | p::pl, s::sl => is_state_valid_after_pop state sl pl
  end.

Property is_state_valid_after_pop_complete state sl pl :
  state_valid_after_pop state sl pl -> is_state_valid_after_pop state sl pl = true.
Proof.
intro.
induction H; intuition.
destruct sl; intuition.
Qed.

(** A state is valid for reducing a production when :
      - The assumptions on the state are such that we will find the right hand
        side of the production on the stack.
      - We will be able to do a goto after having popped the right hand side.
**)
Definition valid_for_reduce (state:state) prod :=
    prefix (rev (prod_rhs prod)) (head_symbs_of_state state)
    /\
    forall state_new,
    state_valid_after_pop state_new
      (rev (prod_rhs prod)) (head_states_of_state state) ->
    goto_table state_new (prod_lhs prod) <> None.

Definition is_valid_for_reduce (state:state) prod:=
  (is_prefix (rev (prod_rhs prod)) (head_symbs_of_state state) &&
   forallb (fun state_new =>
     if is_state_valid_after_pop state_new (rev (prod_rhs prod))
                                           (head_states_of_state state) then
       match goto_table state_new (prod_lhs prod) with
         | None => false
         | Some _ => true
       end
     else
       true)
     all_list)%bool.

Property is_valid_for_reduce_correct (state:state) prod:
  is_valid_for_reduce state prod = true -> valid_for_reduce state prod.
Proof.
unfold is_valid_for_reduce, valid_for_reduce.
intros.
rewrite (Bool.andb_true_iff _ _) in H.
split.
apply is_prefix_correct.
intuition.
intros.
rewrite forallb_forall in H.
destruct H.
specialize (H1 state_new (all_list_forall state_new)).
rewrite is_state_valid_after_pop_complete in H1; intuition.
rewrite H2 in H1; intuition.
Qed.

(** All the states that does a reduce are valid for reduction **)
Definition reduce_ok :=
  forall s,
    match action_table s with
      | inr awp =>
        forall t, match awp t with
          | Reduce_act p => valid_for_reduce s p
          | _ => True
        end
      | inl (Default_reduce_act p) => valid_for_reduce s p
      | _ => True
    end.

Definition is_reduce_ok :=
  forallb (fun s =>
    match action_table s with
      | inr awp =>
        forallb (fun t =>
          match awp t with
            | Reduce_act p => is_valid_for_reduce s p
            | _ => true
          end)
          all_list
      | inl (Default_reduce_act p) => is_valid_for_reduce s p
      | _ => true
    end)
    all_list.

Property is_reduce_ok_correct :
  is_reduce_ok = true -> reduce_ok.
Proof.
unfold is_reduce_ok, reduce_ok.
intros.
rewrite forallb_forall in H.
specialize (H s (all_list_forall s)).
destruct (action_table s).
destruct d; intuition.
apply is_valid_for_reduce_correct; intuition.
intro.
rewrite forallb_forall in H.
specialize (H t (all_list_forall t)).
destruct (a t); intuition.
apply is_valid_for_reduce_correct; intuition.
Qed.

(** The automaton is safe **)
Definition safe :=
  initial_no_accept /\ accept_last_symb /\ accept_initial /\
  shift_head_symbs /\ goto_head_symbs /\ shift_past_state /\
  goto_past_state /\ reduce_ok.

Definition is_safe:=
  (is_initial_no_accept && is_accept_last_symb && is_accept_initial &&
    is_shift_head_symbs && is_goto_head_symbs && is_shift_past_state &&
    is_goto_past_state && is_reduce_ok)%bool.

Property is_safe_correct:
  is_safe = true -> safe.
Proof.
unfold safe, is_safe.
repeat rewrite Bool.andb_true_iff.
intuition.
apply is_initial_no_accept_correct; assumption.
apply is_accept_last_symb_correct; assumption.
apply is_accept_initial_correct; assumption.
apply is_shift_head_symbs_correct; assumption.
apply is_goto_head_symbs_correct; assumption.
apply is_shift_past_state_correct; assumption.
apply is_goto_past_state_correct; assumption.
apply is_reduce_ok_correct; assumption.
Qed.

End Make.
