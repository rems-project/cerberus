Require Import Streams.
Require Import List.
Require Import Syntax.
Require Import Equality.
Require Import Alphabet.
Require Grammar.
Require Automaton.
Require Interpreter.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).

(** * Correctness of the interpreter **)

(** We prove that, in any case, if the interpreter accepts returning a
    semantic value, then this is a semantic value of the input **)

(** [word_has_stack_semantics] relates a word with a state, stating that the
    word is a concatenation of words that have the semantic values stored in
    the stack. **)
Inductive word_has_stack_semantics:
  forall (word:list token) (stack:stack), Prop :=
  | Nil_stack_whss: word_has_stack_semantics [] Nil_stack
  | Cons_stack_whss:
    forall (wordq:list token) (stackq:stack),
      word_has_stack_semantics wordq stackq ->

    forall (wordt:list token) (s:noninitstate)
           (semantic_valuet:_),
      inhabited (parse_tree (last_symb_of_non_init_state s) wordt semantic_valuet) ->

    word_has_stack_semantics
       (wordq++wordt) (Cons_stack s semantic_valuet stackq).

(** [pop] preserves the invariant **)
Lemma pop_invariant
  (symbols_to_pop:list symbol)
  (stack_cur:stack)
  (symbols_popped:list symbol)
  (sem_popped:tuple (List.map symbol_semantic_type symbols_popped)):
  match pop symbols_to_pop stack_cur _ sem_popped with
    | OK (stack_new, sem) =>
      forall word1 word2,
        word_has_stack_semantics word1 stack_cur ->
        inhabited (parse_tree_list symbols_popped word2 sem_popped) ->
          exists word1res word2res,
            inhabited
              (parse_tree_list (rev_append symbols_to_pop symbols_popped) word2res sem) /\
            (word1 ++ word2 = word1res ++ word2res)%list /\
            word_has_stack_semantics word1res stack_new
    | Err => True
  end.
Proof.
revert stack_cur symbols_popped sem_popped.
induction symbols_to_pop.
simpl; intros.
exists word1 word2.
now intuition.
intros.
unfold pop.
destruct stack_cur.
now exact I.
fold pop.
destruct (compare_eqdec (last_symb_of_non_init_state state_cur) a).
destruct e.
specialize (IHsymbols_to_pop stack_cur (last_symb_of_non_init_state state_cur::symbols_popped) (s, sem_popped)).
unfold eq_rect.
revert IHsymbols_to_pop.
pose (pop symbols_to_pop stack_cur (_::_) (s, sem_popped)).
change Type with Type in *.
fold r.
destruct r.
now intuition.
destruct p.
intros.
dependent destruction H.
rewrite <- app_assoc.
apply IHsymbols_to_pop.
now assumption.
destruct H1, H0.
apply inhabits.
apply (Cons_ptl wordt); assumption.
now exact I.
Qed.

(** [reduce] preserves the invariant **)
Lemma reduce_invariant (stack:stack) (prod:production):
 forall word,
   word_has_stack_semantics word stack ->
   match reduce stack prod with
    | OK stack_new =>
      word_has_stack_semantics word stack_new
    | Err => True
   end.
Proof.
intros.
unfold reduce.
pose proof (pop_invariant (rev (prod_rhs prod)) stack [] ()).
destruct (pop (rev (prod_rhs prod)) stack [] ()); intuition.
destruct p.
intros.
unfold bind2.
destruct (goto_table (state_of_stack s) (prod_lhs prod)); intuition.
destruct s0.
destruct (H0 word [] H (inhabits Nil_ptl)).
destruct H1.
intuition.
rewrite app_nil_r in H1.
rewrite H1.
apply Cons_stack_whss; intuition.
rewrite e.
clear H0.
revert t H2.
rewrite (rev_append_rev_inverse _ (prod_rhs prod)).
unfold eq_rect_r, Logic.eq_sym, eq_rect.
intros.
destruct H2; apply inhabits.
now apply Non_terminal_pt; assumption.
Qed.

(** [step] preserves the invariant **)
Lemma step_invariant (stack:stack) (buffer:Stream token):
  forall buffer_tmp,
  (exists word_old,
    buffer = word_old ++ buffer_tmp /\
    word_has_stack_semantics word_old stack) ->
  match step stack buffer_tmp with
    | OK (Accept_sr sem buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        inhabited (parse_tree start_symbol word_new sem)
    | OK (Progress_sr stack_new buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        word_has_stack_semantics word_new stack_new
    | Err | OK Fail_sr => True
  end.
Proof.
intros.
destruct H, H.
unfold step.
destruct (action_table (state_of_stack stack)).
destruct d.
pose proof (reduce_invariant stack p x).
destruct (reduce stack p); intuition.
exists x.
now intuition.
destruct stack; intuition.
destruct stack0; intuition.
destruct (compare_eqdec (last_symb_of_non_init_state state_cur) start_symbol); intuition.
destruct e.
exists x.
intuition.
dependent destruction H0.
inversion H0.
exact H1.
destruct buffer_tmp.
unfold Streams.hd.
destruct t.
destruct (a x0); intuition.
exists (x ++ [existT (fun t => symbol_semantic_type (T t)) x0 s])%list.
split.
now rewrite <- app_str_app_assoc; intuition.
apply Cons_stack_whss; intuition.
rewrite e.
unfold eq_rect_r.
simpl.
now exact (inhabits (Terminal_pt _ _)).
pose proof (reduce_invariant stack p x).
destruct (reduce stack p); intuition.
now exists x; intuition.
Qed.

(** The interpreter is correct : if it returns a semantic value, then the input
    word has this semantic value.
**)
Theorem parse_correct buffer n_steps:
  match parse buffer n_steps with
    | OK (Parsed_pr sem buffer_new) =>
      exists word_new,
        buffer = word_new ++ buffer_new /\
        has_semantic_value word_new sem
    | _ => True
  end.
Proof.
unfold parse.
assert (exists w, buffer = w ++ buffer /\
                  word_has_stack_semantics w Nil_stack).
exists ([]:list token); intuition.
now apply Nil_stack_whss.
revert H.
generalize Nil_stack, buffer at 2 3.
induction n_steps; simpl; intuition.
pose proof (step_invariant _ _ _ H).
destruct (step s buffer0); simpl; intuition.
destruct s0; intuition.
apply IHn_steps; intuition.
Qed.

End Make.
