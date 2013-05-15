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

Require Grammar.
Require Import Orders.
Require Export Alphabet.
Require Export List.
Require Export Syntax.

Module Type AutInit.
  (** The grammar of the automaton. **)
  Declare Module Gram:Grammar.T.
  Export Gram.

  (** The set of non initial state is considered as an alphabet. **)
  Parameter noninitstate : Type.
  Declare Instance NonInitStateAlph : Alphabet noninitstate.

  (** When we are at this state, we know that this symbol is the top of the
     stack. **)
  Parameter last_symb_of_non_init_state: noninitstate -> symbol.
End AutInit.

Module Types(Import Init:AutInit).
  (** In many ways, the behaviour of the initial state is different from the
     behaviour of the other states. So we have chosen to explicitaly separate
     them: the user has to provide the type of non initial states. **)
  Inductive state :=
    | Init: state
    | Ninit: noninitstate -> state.

  Program Instance StateAlph : Alphabet state :=
    { AlphabetComparable := {| compare := fun x y =>
        match x, y return comparison with
          | Init, Ninit _ => Lt
          | Init, Init => Eq
          | Ninit _, Init => Gt
          | Ninit x, Ninit y => compare x y
        end |};
      AlphabetFinite := {| all_list := Init :: map Ninit all_list |} }.
  Local Obligation Tactic := intros.
  Next Obligation.
  destruct x, y; intuition.
  apply compare_antisym.
  Qed.
  Next Obligation.
  destruct x, y, z; intuition.
  rewrite <- H in H0; discriminate.
  rewrite <- H in H0; discriminate.
  apply (compare_trans _ n0); intuition.
  Qed.
  Next Obligation.
  intros x y.
  destruct x, y; intuition; try discriminate.
  rewrite (compare_eq n n0); intuition.
  Qed.
  Next Obligation.
  destruct x; intuition.
  right.
  apply in_map.
  apply all_list_forall.
  Qed.

  Coercion Ninit : noninitstate >-> state.

  (** For an LR automaton, there are four kind of actions that can be done at a
     given state:
       - Shifting, that is reading a token and putting it into the stack,
       - Reducing a production, that is popping the right hand side of the
          production from the stack, and pushing the left hand side,
       - Failing
       - Accepting the word

     As in the menhir parser generator, we do not want our parser to read after
     the end of stream. That means that once the parser has read a word in the
     grammar language, it should stop without peeking the input stream. So, for
     the automaton to be complete, the grammar must be particular: if a word is
     in its language, then it is not a prefix of an other word of the language
     (otherwise, menhir reports an end of stream conflict).

     As a consequence of that, there is two notions of action: the first one is
     an action performed before having read the stream, the second one is after
  **)

  Inductive action (term:terminal) :=
  | Shift_act: forall s:noninitstate,
                 last_symb_of_non_init_state s = T term -> action term
  | Reduce_act: production -> action term
  | Fail_act: action term.
  Implicit Arguments Shift_act [term].
  Implicit Arguments Reduce_act [term].
  Implicit Arguments Fail_act [term].

  Inductive default_action :=
  | Default_reduce_act: production -> default_action
  | Accept_act: default_action.

  (** Types used for the annotations of the automaton. **)

  (** We have to introduce the notion of pseudo-production : it is either a
     production, either [None]. Intuitively, None denotes the "production"
     reduced by an accept action **)
  Definition pseudoprod := option production.

  (** An item is a part of the annotations given to the validator.
     It is acually a set of LR(1) items sharing the same core. It is needed 
     to validate completeness. **)
  Record item := {
  (** The pseudo-production of the item. **)
    pseudoprod_item: pseudoprod;

  (** The position of the dot. **)
    dot_pos_item: nat;

  (** The lookahead symbol of the item. We are using a list, so we can store
     together multiple LR(1) items sharing the same core. **)
    lookaheads_item: list terminal
  }.
End Types.

Module Type T.
  Include AutInit <+ Types.
  Module Export GramDefs := Grammar.Defs Gram.

  (** The action table maps a state to either a map terminal -> action (we have
     to peek) or a default action (we do not have to peek). **)
  Parameter action_table: 
    state -> default_action + (forall term:terminal, action term).
  (** The goto table of an LR(1) automaton. **)
  Parameter goto_table: state -> forall nt:nonterminal,
    option { s:noninitstate | last_symb_of_non_init_state s = NT nt }.

  (** Some annotations on the automaton to help the validation. **)

  (** When we are at this state, we know that these symbols are just below
     the top of the stack. The list is ordered such that the head correspond
     to the (almost) top of the stack. **)
  Parameter past_symb_of_non_init_state: noninitstate -> list symbol.

  (** When we are at this state, the (strictly) previous states verify these
     predicates. **)
  Parameter past_state_of_non_init_state: noninitstate -> list (state -> bool).

  (** The items of the state. **)
  Parameter items_of_state: state -> list item.

  (** The nullable predicate for non terminals :
     true if and only if the symbol produces the empty string **)
  Parameter nullable_nterm: nonterminal -> bool.

  (** The first predicates for non terminals, symbols or words of symbols. A
     terminal is in the returned list if, and only if the parameter produces a
     word that begins with the given terminal **)
  Parameter first_nterm: nonterminal -> list terminal.
End T.
