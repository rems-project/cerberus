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
Require Automaton.
Require Import Alphabet.

Module Make(Import A:Automaton.T).

(** The error monad **)
Inductive result (A:Type) :=
  | Err: result A
  | OK: A -> result A.

Implicit Arguments Err [A].
Implicit Arguments OK [A].

Definition bind {A B: Type} (f: result A) (g: A -> result B): result B :=
  match f with
    | OK x => g x
    | Err => Err
  end.

Definition bind2 {A B C: Type} (f: result (A * B)) (g: A -> B -> result C):
  result C :=
  match f with
    | OK (x, y) => g x y
    | Err => Err
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

(** Some operations on streams **)

(** Concatenation of a list and a stream **)
Fixpoint app_str {A:Type} (l:list A) (s:Stream A) :=
  match l with
    | nil => s
    | cons t q => Cons t (app_str q s)
  end.

Infix "++" := app_str (right associativity, at level 60).

Lemma app_str_app_assoc {A:Type} (l1 l2:list A) (s:Stream A) :
  l1 ++ (l2 ++ s) = (l1 ++ l2) ++ s.
Proof.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

(** The stack of the automaton : it can be either nil or contains a non
    initial state, a semantic value for the symbol associted with this state,
    and a nested stack. **)
Inductive stack :=
  | Nil_stack: stack
  | Cons_stack:
    forall state_cur: noninitstate,
      symbol_semantic_type (last_symb_of_non_init_state state_cur) ->
      stack -> stack.

(** The top state of a stack **)
Definition state_of_stack (stack:stack): state :=
  match stack with
    | Nil_stack => Init
    | Cons_stack s _ _ => s
  end.

(** [pop] pops some symbols from the stack. It returns the popped semantic
    values using [sem_popped] as an accumulator and discards the popped
    states.**)
Fixpoint pop
  (symbols_to_pop:list symbol) (stack_cur:stack)
  (symbols_popped:list symbol)
  (sem_popped:tuple (List.map symbol_semantic_type symbols_popped)):
    result (stack * tuple (List.map symbol_semantic_type
                                    (rev_append symbols_to_pop symbols_popped))) :=
  match symbols_to_pop with
    | [] => OK (stack_cur, sem_popped)
    | t::q =>
      match stack_cur with
        | Cons_stack state_cur sem stack_rec =>
          match compare_eqdec (last_symb_of_non_init_state state_cur) t with
            | left e =>
              let sem_conv :=
                eq_rect _ (fun s => symbol_semantic_type s) sem _ e
              in
              let res :=
                pop q stack_rec
                    (t :: symbols_popped)
                    (sem_conv, sem_popped)
              in
              res
            | right _ => Err
          end
        | Nil_stack => Err
      end
  end.

Lemma rev_append_rev_inverse :
  forall T (l:list T), rev_append (rev l) [] = l.
Proof.
intros.
rewrite <- rev_alt.
apply rev_involutive.
Qed.

(** [reduce] does the reduction action :
      - pops some elements from the stack
      - follows the goto for the produced non terminal symbol **)
Definition reduce (stack_cur:stack) production: result stack :=
  do (stack_new, sem) <- pop (rev (prod_rhs production)) stack_cur [] ();
  match goto_table (state_of_stack stack_new) (prod_lhs production) with
    | Some (exist state_new e) =>
      let act := eq_rect_r (fun s => _ (_ s)) (prod_action production) e in
      let sem_conv :=
        eq_rect _ (fun l => _ (List.map _ l)) sem _ (rev_append_rev_inverse _ _) in
      OK (Cons_stack
            state_new
            (uncurry act sem_conv)
            stack_new)
    | None => Err
  end.

(** [step_result] represents the result of one step of the automaton : it can
    fail, accept or progress. [Fail_sr] means that the input is incorrect.
    [Accept_sr] means that this is the last step of the automaton, and it
    returns the semantic value of the input word. [Progress_sr] means that
    some progress has been made, but new steps are needed in order to accept
    a word.

    For [Accept_sr] and [Progress_sr], the result contains the new input buffer.

    [Fail_sr] means that the input word is rejected by the automaton. It is
    different to [Err] (from the error monad), which mean that the automaton is
    bogus and has perfomed a forbidden action. **)

Inductive step_result :=
  | Fail_sr: step_result
  | Accept_sr: symbol_semantic_type start_symbol -> Stream token -> step_result
  | Progress_sr: stack -> Stream token -> step_result.

(** One step of parsing. **)
Definition step stack_cur buffer: result step_result :=
  match action_table (state_of_stack stack_cur) with
    | inl (Default_reduce_act production) =>
      do stack_new <- reduce stack_cur production;
      OK (Progress_sr stack_new buffer)
    | inl Accept_action =>
      match stack_cur with
        | Cons_stack s sem Nil_stack =>
          match compare_eqdec (last_symb_of_non_init_state s) start_symbol with
            | left e =>
              let sem_conv := eq_rect _ (fun s => _ s) sem _ e in
              OK (Accept_sr sem_conv buffer)
            | right _ => Err
          end
        | _ => Err
      end
    | inr awt =>
      match Streams.hd buffer with
        | existT term sem =>
          match awt term with
            | Shift_act state_new e =>
              let sem_conv := eq_rect_r (fun s => _ s) sem e in
              OK (Progress_sr (Cons_stack state_new sem_conv stack_cur)
                              (Streams.tl buffer))
            | Reduce_act production =>
              do stack_new <- reduce stack_cur production;
              OK (Progress_sr stack_new buffer)
            | Fail_action =>
              OK Fail_sr
          end
      end
  end.

(** The parsing use a [nat] parameter [n_steps], so that we do not have to prove
    terminaison, which is difficult. So the result of a parsing is either
    a failure (the automaton has rejected the input word), either a timeout
    (the automaton has spent all the given [n_steps]), either a parsed semantic
    value with a rest of the input buffer.
**)
Inductive parse_result :=
  | Fail_pr: parse_result
  | Timeout_pr: parse_result
  | Parsed_pr: symbol_semantic_type start_symbol -> Stream token -> parse_result.

Fixpoint parse_fix stack_cur buffer n_steps: result parse_result:=
  match n_steps with
    | O => OK Timeout_pr
    | S it =>
      do r <- step stack_cur buffer;
      match r with
        | Fail_sr => OK Fail_pr
        | Accept_sr t buffer_new => OK (Parsed_pr t buffer_new)
        | Progress_sr s buffer_new => parse_fix s buffer_new it
      end
  end.

Definition parse buffer n_steps: result parse_result :=
  parse_fix Nil_stack buffer n_steps.

End Make.

Module Type T(A:Automaton.T).
  Include (Make A).
End T.
