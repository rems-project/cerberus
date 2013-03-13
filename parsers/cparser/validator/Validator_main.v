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
Require Automaton.
Require Interpreter_safe.
Require Interpreter_correct.
Require Interpreter_complete.

Module Make(Export Aut:Automaton.T).
Export Aut.Gram.
Export Aut.GramDefs.

Module Import Inter := Interpreter.Make Aut.
Module Safe := Interpreter_safe.Make Aut Inter.
Module Correct := Interpreter_correct.Make Aut Inter.
Module Complete := Interpreter_complete.Make Aut Inter.

Definition complete_validator:bool := Complete.Valid.is_complete.
Definition safe_validator:bool := Safe.Valid.is_safe.
Definition parse (safe:safe_validator=true) n_steps buffer : parse_result :=
  Safe.parse_with_safe (Safe.Valid.is_safe_correct safe) buffer n_steps.

(** Correction theorem. **)
Theorem parse_correct
  (safe:safe_validator = true) n_steps buffer:
  match parse safe n_steps buffer with
    | Parsed_pr sem buffer_new =>
      exists word,
        buffer = word ++ buffer_new /\ has_semantic_value word sem
    | _ => True
  end.
Proof.
unfold parse, Safe.parse_with_safe.
pose proof (Correct.parse_correct buffer n_steps).
generalize (Safe.parse_no_err buffer n_steps (Safe.Valid.is_safe_correct safe)).
destruct (Inter.parse buffer n_steps); intros.
now destruct (n (eq_refl _)).
now destruct p; trivial.
Qed.

(** Completeness theorem. **)
Theorem parse_complete
  (safe:safe_validator = true) n_steps word buffer_end sem:
  complete_validator = true ->
  forall tree:parse_tree start_symbol word sem,
  match parse safe n_steps (word ++ buffer_end) with
    | Fail_pr => False
    | Parsed_pr sem_res buffer_end_res =>
      sem_res = sem /\ buffer_end_res = buffer_end /\ n_steps >= parse_tree_size tree+2
    | Timeout_pr => n_steps < parse_tree_size tree+2
  end.
Proof.
intros.
unfold parse, Safe.parse_with_safe.
pose proof (Complete.parse_complete word buffer_end n_steps sem (Complete.Valid.is_complete_correct H) tree).
generalize (Safe.parse_no_err (word ++ buffer_end) n_steps (Safe.Valid.is_safe_correct safe)).
destruct (Inter.parse (word ++ buffer_end) n_steps); intros.
now destruct (n eq_refl).
now exact H0.
Qed.

(** Unambiguity theorem. **)
Theorem unambiguity:
  safe_validator = true -> complete_validator = true -> inhabited token ->
  forall word,
  forall sem1 (tree1:parse_tree start_symbol word sem1),
  forall sem2 (tree2:parse_tree start_symbol word sem2),
  sem1 = sem2.
Proof.
intros.
destruct H1.
pose proof (parse_complete H (parse_tree_size tree1+2) word (Streams.const X) sem1) H0 tree1.
pose proof (parse_complete H (parse_tree_size tree1+2) word (Streams.const X) sem2) H0 tree2.
destruct (parse H (parse_tree_size tree1+2) (word ++ Streams.const X)); intuition.
rewrite <- H3, H1; reflexivity.
Qed.

End Make.
