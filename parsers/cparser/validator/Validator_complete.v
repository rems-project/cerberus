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

(** We instantiate some sets/map. **)
Module TerminalComparableM <: ComparableM.
  Definition t := terminal.
  Instance tComparable : Comparable t := _.
End TerminalComparableM.
Module TerminalOrderedType := OrderedType_from_ComparableM TerminalComparableM.
Module StatePseudoprodPosComparableM <: ComparableM.
  Definition t := (state*pseudoprod*nat)%type.
  Instance tComparable : Comparable t := _.
End StatePseudoprodPosComparableM.
Module StatePseudoprodPosOrderedType :=
  OrderedType_from_ComparableM StatePseudoprodPosComparableM.

Module TerminalSet := FSetAVL.Make TerminalOrderedType.
Module StatePseudoprodPosMap := FMapAVL.Make StatePseudoprodPosOrderedType.

(** A pseudo-production is either a production or the thing with is "reduced" by
    an accept action. This function returns its right hand side. **)
Definition pseudoprod_rhs pseudoprod :=
  match pseudoprod with
    | None => [start_symbol]
    | Some prod => prod_rhs prod
  end.

(** Nullable predicate for symbols and list of symbols. **)
Definition nullable_symb (symbol:symbol) :=
  match symbol with
    | NT nt => nullable_nterm nt
    | _ => false
  end.

Definition nullable_word (word:list symbol) :=
  forallb nullable_symb word.

(** First predicate for non terminal, symbols and list of symbols, given as FSets. **)
Definition first_nterm_set (nterm:nonterminal) :=
  fold_left (fun acc t => TerminalSet.add t acc)
    (first_nterm nterm) TerminalSet.empty.

Definition first_symb_set (symbol:symbol) :=
  match symbol with
    | NT nt => first_nterm_set nt
    | T t => TerminalSet.singleton t
  end.

Fixpoint first_word_set (word:list symbol) :=
  match word with
    | [] => TerminalSet.empty
    | t::q =>
      if nullable_symb t then
        TerminalSet.union (first_symb_set t) (first_word_set q)
        else
          first_symb_set t
  end.

(** Small helper for finding the part of an item that is after the dot. **)
Definition future_of_pseudoprod pseudoprod dot_pos : list symbol :=
  (fix loop n lst :=
    match n with
      | O => lst
      | S x => match loop x lst with [] => [] | _::q => q end
    end)
  dot_pos (pseudoprod_rhs pseudoprod).

(** We build a fast map to store all the items of all the states. **)
Definition items_map: StatePseudoprodPosMap.t TerminalSet.t :=
  fold_left (fun acc state =>
    fold_left (fun acc item =>
      let key := (state, pseudoprod_item item, dot_pos_item item) in
        let data := fold_left (fun acc t => TerminalSet.add t acc)
          (lookaheads_item item) TerminalSet.empty
        in
        let old :=
          match StatePseudoprodPosMap.find key acc with
            | Some x => x | None => TerminalSet.empty
          end
        in
        StatePseudoprodPosMap.add key (TerminalSet.union data old) acc
    ) (items_of_state state) acc
  ) all_list (StatePseudoprodPosMap.empty TerminalSet.t).

(** Accessor. **)
Definition find_items_map state pseudoprod dot_pos : TerminalSet.t :=
  match StatePseudoprodPosMap.find (state, pseudoprod, dot_pos) items_map with
    | None => TerminalSet.empty
    | Some x => x
  end.

Definition state_has_future (state:state) (pseudoprod:pseudoprod)
                            (fut:list symbol) (lookahead:terminal) :=
  exists dot_pos:nat,
    fut = future_of_pseudoprod pseudoprod dot_pos /\
    TerminalSet.In lookahead (find_items_map state pseudoprod dot_pos).

(** Iterator over items. **)
Definition forallb_items (P:state -> pseudoprod -> nat -> TerminalSet.t -> bool): bool:=
  StatePseudoprodPosMap.fold (fun key set acc =>
    match key with (st, mp, pos) => (acc && P st mp pos set)%bool end
  ) items_map true.

Lemma forallb_items_spec :
  forall p, forallb_items p = true ->
  forall st mp fut lookahead, state_has_future st mp fut lookahead ->
  forall P:state -> pseudoprod -> list symbol -> terminal -> Prop,
  (forall st mp pos set lookahead,
    TerminalSet.In lookahead set -> p st mp pos set = true ->
      P st mp (future_of_pseudoprod mp pos) lookahead) ->
   P st mp fut lookahead.
Proof.
intros.
unfold forallb_items in H.
rewrite StatePseudoprodPosMap.fold_1 in H.
destruct H0; destruct H0.
specialize (H1 st mp x _ _ H2).
destruct H0.
apply H1.
unfold find_items_map in *.
pose proof (@StatePseudoprodPosMap.find_2 _ items_map (st, mp, x)).
destruct (StatePseudoprodPosMap.find (st, mp, x) items_map); [ |destruct (TerminalSet.empty_1 H2)].
specialize (H0 _ (eq_refl _)).
pose proof (StatePseudoprodPosMap.elements_1 H0).
revert H.
generalize true at 1.
induction H3.
destruct H.
destruct y.
simpl in H3; destruct H3.
pose proof (compare_eq (st, mp, x) k H).
destruct H3.
simpl.
generalize (p st mp x t).
induction l; simpl; intros.
rewrite Bool.andb_true_iff in H3.
intuition.
destruct a; destruct k; destruct p0.
simpl in H3.
replace (b0 && b && p s p0 n t0)%bool with (b0 && p s p0 n t0 && b)%bool in H3.
apply (IHl _ _ H3).
destruct b, b0, (p s p0 n t0); reflexivity.
intro.
apply IHInA.
Qed.

(** * Validation for completeness **)

(** The nullable predicate is a fixpoint : it is correct. **)
Definition nullable_stable:=
  forall p:production,
    nullable_word (prod_rhs p) = true ->
    nullable_nterm (prod_lhs p) = true.

Definition is_nullable_stable :=
  forallb (fun p:production =>
    implb (nullable_word (prod_rhs p)) (nullable_nterm (prod_lhs p)))
    all_list.

Property is_nullable_stable_correct :
  is_nullable_stable = true -> nullable_stable.
Proof.
unfold is_nullable_stable, nullable_stable.
intros.
rewrite forallb_forall in H.
specialize (H p (all_list_forall p)).
rewrite H0 in H; intuition.
Qed.

(** The first predicate is a fixpoint : it is correct. **)
Definition first_stable:=
  forall (p:production),
    TerminalSet.Subset (first_word_set (prod_rhs p))
                       (first_nterm_set (prod_lhs p)).

Definition is_first_stable :=
  forallb (fun p:production =>
    TerminalSet.subset (first_word_set (prod_rhs p))
                       (first_nterm_set (prod_lhs p)))
    all_list.

Property is_first_stable_correct :
  is_first_stable = true -> first_stable.
Proof.
unfold is_first_stable, first_stable.
intros.
rewrite forallb_forall in H.
specialize (H p (all_list_forall p)).
apply TerminalSet.subset_2; intuition.
Qed.

(** If a state contains the item _->S., where S is the start symbol, then
    the corresponding item has no lookahead symbol (end of the word), and the
    state does an [Accept_act] **)
Definition end_accept :=
  forall (state:state) pseudoprod fut lookahead,
    state_has_future state pseudoprod fut lookahead ->
    pseudoprod = None -> fut = [] ->
    action_table state = inl Accept_act.

Definition is_end_accept :=
  forallb_items (fun st mp pos lset =>
    match mp, future_of_pseudoprod mp pos with
      | None, [] =>
        match action_table st with
           | inl Accept_act => true
           | _ => false
         end
      | _, _ => true
    end).

Property is_end_accept_correct :
  is_end_accept = true -> end_accept.
Proof.
unfold is_end_accept, end_accept.
intros.
revert H1 H2.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ _ _ => _)).
intros.
rewrite H3 in *; rewrite H4 in *; clear H3 H4 mp.
destruct (action_table st); try destruct d; try discriminate; reflexivity.
Qed.

(** The initial state has the _=>.S item, where S is the start symbol **)
Definition start_future :=
  forall t:terminal, state_has_future Init None [start_symbol] t.

Definition is_start_future :=
  forallb (fun t => TerminalSet.mem t (find_items_map Init None 0)) all_list.

Property is_start_future_correct :
  is_start_future = true -> start_future.
Proof.
exists 0.
split.
reflexivity.
unfold is_start_future in H.
rewrite forallb_forall in H.
apply TerminalSet.mem_2.
apply H.
apply all_list_forall.
Qed.

(** If a state contains an item of the form A->_.av[[b]], where a is a
    terminal, then reading an a does a [Shift_act], to a state containing
    an item of the form A->_.v[[b]]. **)
Definition terminal_shift :=
  forall (s1:state) pseudoprod fut lookahead,
    state_has_future s1 pseudoprod fut lookahead ->
    match fut with
      | T t::q =>
        match action_table s1 with
          | inr awp =>
            match awp t with
              | Shift_act s2 _ =>
                state_has_future s2 pseudoprod q lookahead
              | _ => False
            end
          | _ => False
        end
      | _ => True
    end.

Definition is_terminal_shift:=
  forallb_items (fun s1 mp pos lset =>
    match future_of_pseudoprod mp pos with
      | T t::_ =>
        match action_table s1 with
          | inr awp =>
            match awp t with
              | Shift_act s2 _ =>
                TerminalSet.subset lset (find_items_map s2 mp (S pos))
              | _ => false
            end
          | _ => false
        end
      | _ => true
    end).

Property is_terminal_shift_correct :
  is_terminal_shift = true -> terminal_shift.
Proof.
unfold is_terminal_shift, terminal_shift.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ _ _ => _)).
intros.
destruct (future_of_pseudoprod mp pos) as [] _eqn; intuition.
destruct s; intuition.
destruct (action_table st); intuition.
destruct (a t); intuition.
exists (S pos).
split.
unfold future_of_pseudoprod in *.
rewrite Heql; reflexivity.
apply (TerminalSet.subset_2 H2); intuition.
Qed.

(** If a state contains an item of the form A->_.[[a]], then either we do a
    [Default_reduce_act] of the corresponding production, either a is a
    terminal (ie. there is a lookahead terminal), and reading a does a
    [Reduce_act] of the corresponding production. **)
Definition end_reduce :=
  forall (s:state) pseudoprod fut lookahead,
    state_has_future s pseudoprod fut lookahead ->
    fut = [] ->
    match pseudoprod with
      | Some p1 =>
        match action_table s with
          | inl (Default_reduce_act p2) => p1 = p2
          | inr awt =>
            match awt lookahead with
              | Reduce_act p2 => p1 = p2
              | _ => False
            end
          | inl _ => False
        end
      | _ => True
    end.

Definition is_end_reduce :=
  forallb_items (fun s mp pos lset =>
    match future_of_pseudoprod mp pos, mp with
        | [], Some p1 =>
          match action_table s with
            | inl (Default_reduce_act p2) => compare_eqb p1 p2
            | inr awt =>
              TerminalSet.fold (fun lookahead acc =>
                match awt lookahead with
                  | Reduce_act p2 => (acc && compare_eqb p1 p2)%bool
                  | _ => false
                end) lset true
            | inl _ => false
          end
        | _, _ => true
      end).

Property is_end_reduce_correct :
  is_end_reduce = true -> end_reduce.
Proof.
unfold is_end_reduce, end_reduce.
intros.
revert H1.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ _ _ => _)).
intros.
rewrite H3 in H2.
destruct mp; intuition.
destruct (action_table st).
destruct d; intuition.
apply compare_eqb_iff; intuition.
rewrite TerminalSet.fold_1 in H2.
revert H2.
generalize true at 1.
pose proof (TerminalSet.elements_1 H1).
induction H2.
pose proof (compare_eq _ _ H2).
destruct H4.
simpl.
assert (fold_left
     (fun (a0 : bool) (e : TerminalSet.elt) =>
       match a e with
         | Shift_act _ _ => false
         | Reduce_act p2 => (a0 && compare_eqb p p2)%bool
         | Fail_act => false
       end) l false = true -> False).
induction l; intuition.
apply IHl.
simpl in H4.
destruct (a a0); intuition.
destruct (a lookahead0); intuition.
apply compare_eqb_iff.
destruct (compare_eqb p p0); intuition.
destruct b; intuition.
simpl; intros.
apply (IHInA _ H4).
Qed.

(** If a state contains an item of the form A->_.Bv[[b]], where B is a
    non terminal, then the goto table says we have to go to a state containing
    an item of the form A->_.v[[b]]. **)
Definition non_terminal_goto :=
  forall (s1:state) pseudoprod fut lookahead,
    state_has_future s1 pseudoprod fut lookahead ->
    match fut with
      | NT nt::q =>
        match goto_table s1 nt with
          | Some (exist s2 _) =>
            state_has_future s2 pseudoprod q lookahead
          | _ => True
        end
      | _ => True
    end.

Definition is_non_terminal_goto :=
  forallb_items (fun s1 mp pos lset =>
    match future_of_pseudoprod mp pos with
      | NT nt::_ =>
        match goto_table s1 nt with
          | Some (exist s2 _) =>
            TerminalSet.subset lset (find_items_map s2 mp (S pos))
          | _ => true
        end
      | _ => true
    end).

Property is_non_terminal_goto_correct :
  is_non_terminal_goto = true -> non_terminal_goto.
Proof.
unfold is_non_terminal_goto, non_terminal_goto.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ _ _ => _)).
intros.
destruct (future_of_pseudoprod mp pos) as [] _eqn; intuition.
destruct s; intuition.
destruct (goto_table st n); intuition.
destruct s.
exists (S pos).
split.
unfold future_of_pseudoprod in *.
rewrite Heql; reflexivity.
apply (TerminalSet.subset_2 H2); intuition.
Qed.

(** Closure property of item sets : if a state contains an item of the form
    A->_.Bv[[b]], then for each production B->u and each terminal a of
    first(vb), the state contains an item of the form B->_.u[[a]] **)
Definition non_terminal_closed :=
  forall (s1:state) pseudoprod fut lookahead,
    state_has_future s1 pseudoprod fut lookahead ->
    match fut with
      | NT nt::q =>
        forall (p:production) (lookahead2:terminal),
          prod_lhs p = nt ->
            TerminalSet.In lookahead2 (first_word_set q) \/
            lookahead2 = lookahead /\ nullable_word q = true ->
              state_has_future s1 (Some p) (prod_rhs p) lookahead2
      | _ => True
    end.

Definition is_non_terminal_closed :=
  forallb_items (fun s1 mp pos lset =>
    match future_of_pseudoprod mp pos with
        | NT nt::q =>
          forallb (fun p =>
            if compare_eqb (prod_lhs p) nt then
              let lookaheads := find_items_map s1 (Some p) 0 in
              (if nullable_word q then
                TerminalSet.subset lset lookaheads
              else true) &&
              TerminalSet.subset (first_word_set q) lookaheads
            else true
          )%bool all_list
        | _ => true
    end).

Property is_non_terminal_closed_correct:
  is_non_terminal_closed = true -> non_terminal_closed.
Proof.
unfold is_non_terminal_closed, non_terminal_closed.
intros.
apply (forallb_items_spec _ H _ _ _ _ H0 (fun _ _ _ _ => _)).
intros.
destruct (future_of_pseudoprod mp pos); intuition.
destruct s; try exact I.
rewrite forallb_forall in H2.
intro.
specialize (H2 p (all_list_forall p)).
intros.
rewrite <- compare_eqb_iff in H3.
rewrite H3 in H2.
rewrite Bool.andb_true_iff in H2.
exists 0.
split; try reflexivity.
destruct H2, H4.
apply (TerminalSet.subset_2 H5); intuition.
destruct H4; destruct H4.
rewrite H6 in H2.
apply (TerminalSet.subset_2 H2); intuition.
Qed.

(** The automaton is complete **)
Definition complete :=
  nullable_stable /\ first_stable /\ end_accept /\
  start_future /\ terminal_shift /\ end_reduce /\
  non_terminal_goto /\ non_terminal_closed.

Definition is_complete:=
  (is_nullable_stable && is_first_stable && is_end_accept &&
   is_start_future && is_terminal_shift && is_end_reduce &&
   is_non_terminal_goto && is_non_terminal_closed)%bool.

Property is_complete_correct:
  is_complete = true -> complete.
Proof.
unfold is_complete, complete.
repeat rewrite Bool.andb_true_iff.
intuition.
apply is_nullable_stable_correct; assumption.
apply is_first_stable_correct; assumption.
apply is_end_accept_correct; assumption.
apply is_start_future_correct; assumption.
apply is_terminal_shift_correct; assumption.
apply is_end_reduce_correct; assumption.
apply is_non_terminal_goto_correct; assumption.
apply is_non_terminal_closed_correct; assumption.
Qed.

End Make.
