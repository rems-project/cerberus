Require Import Streams.
Require Import Equality.
Require Import List.
Require Import Syntax.
Require Import Alphabet.
Require Grammar.
Require Automaton.
Require Interpreter.
Require Validator_complete.

Module Make(Import A:Automaton.T) (Import Inter:Interpreter.T A).
Module Import Valid := Validator_complete.Make A.

(** * Completeness Proof **)

(** If the nullable predicate has been validated, then it is correct. **)
Lemma nullable_correct:
  nullable_stable ->
  forall head sem word, word = [] ->
    parse_tree head word sem -> nullable_symb head = true
with nullable_correct_list:
  nullable_stable ->
  forall heads sems word, word = [] ->
    parse_tree_list heads word sems -> nullable_word heads = true.
Proof.
intros.
destruct X.
discriminate H0.
apply H.
apply (nullable_correct_list H _ _ _ H0 p0).
intros.
destruct X; simpl; try reflexivity.
apply andb_true_intro.
case_eq wordt; intros; rewrite H1 in H0.
split.
now exact (nullable_correct H _ _ _ H1 p).
now exact (nullable_correct_list H _ _ _ H0 X).
now discriminate H0.
Qed.

(** If the first predicate has been validated, then it is correct. **)
Lemma first_correct:
  nullable_stable -> first_stable ->
  forall head sem word t q, word = t::q ->
  parse_tree head word sem ->
  TerminalSet.In (projT1 t) (first_symb_set head)
with first_correct_list:
  nullable_stable -> first_stable ->
  forall heads sems word t q, word = t::q ->
  parse_tree_list heads word sems ->
  TerminalSet.In (projT1 t) (first_word_set heads).
Proof.
intros.
destruct X.
inversion H1.
destruct H3.
destruct H4.
apply TerminalSet.singleton_2.
apply compare_refl.
apply H0.
now exact (first_correct_list H H0 _ _ _ _ _ H1 p0).
intros.
destruct X.
now discriminate.
simpl.
case_eq wordt; intros.
rewrite (nullable_correct H _ _ _ H2 p).
apply TerminalSet.union_3.
rewrite H2 in H1.
now exact (first_correct_list H H0 _ _ _ _ _ H1 X).
rewrite H2 in H1; inversion H1; destruct H4.
now destruct (nullable_symb head_symbolt); [apply TerminalSet.union_2 | ];
  exact (first_correct H H0 _ _ _ _ _ H2 p).
Qed.

(** ** Helper functions and lemmas **)

(** First terminal of a word **)
Definition first_term_word (word:list token) (follow:terminal): terminal :=
  match word with
    | [] => follow
    | existT t _ :: _ => t
  end.

(** Extends a stack with a list of state and a corresponding tuple of
    semantic values **)
Fixpoint extend_stack stack_cur (states:list noninitstate) :=
  match states
  return tuple (List.map symbol_semantic_type
                 (List.map last_symb_of_non_init_state states)) ->
         stack with
    | [] => fun _ => stack_cur
    | t::q => fun sem =>
      let (semt, semq) := sem in
      Cons_stack t semt (extend_stack stack_cur q semq)
  end.

(** Simple lemma about JM equality and eq_rect **)
Lemma eq_rect_JMeq :
  forall A (x:A) P v y e, eq_rect x P v y e ~= v.
Proof.
intros.
dependent destruction e.
reflexivity.
Qed.

(** ** Completeness invariant **)

(** The completeness is proved by maintaining an invariant : at a given
    instant of the parsing, a part of the data is in the stack, already
    parsed, and the other part is still in the input buffer. We want to prove,
    as an invariant, that both parts seen together always have the same
    semantics. We prove that if this invariant holds, then the parser
    does not produce an error. As a consequence, if the invariant holds
    before the parsing (ie. the input word has the given semantic),
    then either the parser crashes (impossible if the automaton is correct),
    either it does not terminate, either it parses correctly the input.

    We have to formalize this invariant : what we have at any given
    iteration is a partial parsing tree. We can divide each production being
    parsed into three (or two) parts :
      - the already parsed symbols, that are waiting in the stack
      - the non-terminal being parsed, if we are parsing a nested production
        whose left hand side is this non terminal. We call that optionnal part
        the "hole"
      - the symbols to be parsed, for which we assume there is a corresponding
        part in the input buffer.
    The invariant is a list of these data, one cell for each production being
    parsed. We add an extra cell for the pseudo-production containing only the
    start symbol as a right hand side.
**)

(** For each production being parsed, [past_invariant] contains the part of the
    invariant concerning the part of the production already parsed.
**)
Record past_invariant:= {
  (** The intermediate states of the automaton associated to the parsed part
      of the production **)
  states_pi: list noninitstate;

  (** The parsed symbols **)
  symbl_pi := List.map last_symb_of_non_init_state states_pi;

  (** The parsed semantics **)
  sem_pi: tuple (List.map symbol_semantic_type symbl_pi);

  (** The resulting stack, just before parsing the hole **)
  stack_pi stack_top:= extend_stack stack_top states_pi sem_pi
}.

(** The invariant concerning the part of the production that has to be parsed,
    with the hole. If [normalized] is true, either there is nothing left to
    parse for this production (next step is to reduce), or the next symbol is a
    terminal.
**)
Record hole_future_invariant (normalized:bool) := {
  (** The symbols to be parsed, together with the expected semantics. **)
  future_hfi:{symbl: _ & tuple (List.map symbol_semantic_type symbl)};

  (** Proof that we are in a normalized situation, if so. **)
  normalized_proof_hfi:
    match normalized, projT1 future_hfi with
      | true, NT _::_ => False
      | _, _ => True
    end;

  (** The corresponding word (eg. part of the input buffer). **)
  word_future_hfi: list token;

  (** The word has the expected semantics. **)
  future_sem_proof_hfi: parse_tree_list (projT1 future_hfi) word_future_hfi (projT2 future_hfi);

  (** The production of the hole, if so, and the corresponding semantics **)
  hole_hfi: option {prod: _ & tuple (List.map symbol_semantic_type (prod_rhs prod))};

  (** Same information, but with a pseudo-production. **)
  hole_pseudo_hfi: option {pseudoprod: _ &
                          tuple (List.map symbol_semantic_type (pseudoprod_rhs pseudoprod))} :=
    match hole_hfi with
      | Some i => Some (existT _ (Some (projT1 i)) (projT2 i))
      | None => None
    end;

  (** The list of symbols for both the future and the hole. **)
  symbl_hfi: list symbol :=
    match hole_hfi with
      | Some i => NT  (prod_lhs (projT1 i)) :: projT1 future_hfi
      | None => projT1 future_hfi
    end;

  (** The corresponding semantics. **)
  sem_hfi: tuple (List.map symbol_semantic_type symbl_hfi) :=
    match hole_hfi return _ (List.map _ (match hole_hfi with
                          Some i => _ :: _ | _ => _ end)) with
      | Some i =>
        (uncurry (prod_action _) (projT2 i), projT2 future_hfi)
      | None => projT2 future_hfi
    end
}.

(** The completeness invariant itself. It is a list where each cell contain the
    information concerning one pseudo-production being parsed. The list is stored
    backward, so the updates are always done at the tail. **)
Inductive completeness_invariant
    (** The semantic of the whole parsing. **)
    (start_sem:symbol_semantic_type start_symbol)
    
    (** The terminal just following the input word. **)
    (follow: terminal):

    (** The part of the stack of the automaton, and the part of the input
        buffer concerned by this part of the invariant **)
  forall (stack:stack) (word:list token)

    (** In the case this term is only a part of the invariant, and reprensents
        only the less nested incompletly parsed productions, this parameter
        contains the next nested production and the associated semantics (ie.
        the hole in the production). **)
         (hole_info: option {pseudoprod:_ &
              tuple (List.map symbol_semantic_type (pseudoprod_rhs pseudoprod))})

    (** If this parameter is [true], then the previous parameter is [None],
        and either there are no more symbols to parse in the current,
        production, or the next symbol to parse is a terminal. Before proving
        the parsing of a non-terminal, we have to unfold its parsing tree in
        the invariant. That is called the "normalization" of the invariant. **)
         (normalized:bool)

    (** The number of steps needed to complete the parsing of all the 
        pseudo-production contained in this invariant. **)
         (n_steps:nat),
    Prop :=

  (** Base case of the invariant : simply a hole requesting the start
      pseudo-production **)
  | Nil_pstz:
    completeness_invariant start_sem follow Nil_stack []
                           (Some (existT _ None (start_sem,()))) false 1

  (** Cons case of the invariant. **)
  | Cons_pstz:
    (** The pseudo-production we are talking about, and the current semantics. **)
    forall (pseudoprod:pseudoprod)
           (semantics:tuple (List.map symbol_semantic_type (pseudoprod_rhs pseudoprod)))
       (** The part of the stack and the word associated to the production in
           which the current production is nested. **)
           (stack_top:stack)
           (word_top:list token)

       (** Is it normalized ? **)
           (normalized:bool)

       (** Number of steps needed for the nested invariant. **)
           (n_steps:nat)

       (** Information and proofs associated to the parsed part of
           [pseudoprod]. **)
           (past_invariant:past_invariant)

       (** Information and proofs associated to the hole and to the part of
           [pseudoprod] to be parsed. **)
           (hole_future_invariant:hole_future_invariant normalized),

    (** Equalities between the symbols and semantics from the previous parameters
        and the right hand side of [pseudoprod]. **)
    rev_append (symbl_pi past_invariant) (symbl_hfi _ hole_future_invariant) =
      pseudoprod_rhs pseudoprod ->
    semantics ~= tuple_rev_app _ (sem_pi past_invariant)
                               _ (sem_hfi _ hole_future_invariant) ->

    (** Compatibility of the top state of the stack. **)
    state_has_future (state_of_stack (stack_pi past_invariant stack_top))
      pseudoprod (symbl_hfi _ hole_future_invariant) (first_term_word word_top follow) ->

    (** The invariant in which we are nested (we store the invariant
        backwards) **)
    completeness_invariant start_sem follow
      stack_top word_top (Some (existT _ pseudoprod semantics)) false n_steps ->

    completeness_invariant start_sem follow
      (stack_pi past_invariant stack_top)
      (word_future_hfi _ hole_future_invariant++word_top)
      (hole_pseudo_hfi _ hole_future_invariant)
      normalized
      (S (parse_tree_list_size (future_sem_proof_hfi _ hole_future_invariant)+n_steps)).

(** ** Proof of the invariant **)

Lemma pop_complete
  (stack_top:stack)
  (states_to_pop:list noninitstate)
  (sem_to_pop:tuple (List.map symbol_semantic_type
                      (List.map last_symb_of_non_init_state states_to_pop)))
  (symbols_to_pop:list symbol)
  (symbols_popped:list symbol)
  (sem_popped:tuple (List.map symbol_semantic_type symbols_popped)):

  List.map last_symb_of_non_init_state states_to_pop = symbols_to_pop ->

  match pop symbols_to_pop
            (extend_stack stack_top states_to_pop sem_to_pop) _ sem_popped
  with
    | OK (stack_new, sem) =>
      stack_new = stack_top /\
      sem ~= tuple_rev_app _ sem_to_pop _ sem_popped
    | _ => True
  end.
Proof.
revert states_to_pop sem_to_pop symbols_popped sem_popped.
induction symbols_to_pop; destruct states_to_pop; intros; simplify_eq H; intros.
split; reflexivity.
destruct sem_to_pop.
unfold extend_stack, pop, eq_rect.
rewrite <- H0 in *.
destruct (compare_eqdec (last_symb_of_non_init_state n) (last_symb_of_non_init_state n)).
dependent destruction e.
now apply (IHsymbols_to_pop _ f (_::_) (s, sem_popped) H1).
now exact I.
Qed.

Lemma reduce_complete
  (start_sem:symbol_semantic_type start_symbol)
  (follow:terminal)
  (word_top:list token)
  (stack_top:stack)
  (past_invariant:past_invariant)
  (prod:production)
  (semantics:tuple (List.map symbol_semantic_type (prod_rhs prod)))
  (n_steps:nat):

  non_terminal_goto ->

  state_has_future (state_of_stack (stack_pi past_invariant stack_top))
    (Some prod) [] (first_term_word word_top follow) ->

  symbl_pi past_invariant = rev (prod_rhs prod) ->
  semantics ~= tuple_rev_app _ (sem_pi past_invariant) [] () ->

  completeness_invariant start_sem follow
    stack_top word_top (Some (existT _ (Some prod) semantics)) false n_steps ->

  match reduce (stack_pi past_invariant stack_top) prod with
    | OK stack_new => completeness_invariant start_sem follow stack_new word_top None false n_steps
    | Err => True
  end.
Proof.
intros.
unfold reduce.
pose proof (pop_complete stack_top (states_pi past_invariant) (sem_pi past_invariant) (rev (prod_rhs prod)) [] ()).
fold (stack_pi past_invariant stack_top) in H4.
destruct (pop (rev (prod_rhs prod)) (stack_pi past_invariant stack_top) [] ()).
now exact I.
destruct p.
unfold bind2.
dependent destruction H3.
specialize (H _ _ _ _ H6).
unfold symbl_hfi in H.
unfold hole_pseudo_hfi in x.
destruct (hole_hfi _ hole_future_invariant0) as [] _eqn;[.. | discriminate x].
destruct (H4 H1).
rewrite <- H8 in H.
injection x; intro.
rewrite H10 in H.
destruct (goto_table (state_of_stack s) (prod_lhs prod)).
destruct s1.
pose (Build_hole_future_invariant false
      _ (normalized_proof_hfi _ hole_future_invariant0)
      _ (future_sem_proof_hfi _ hole_future_invariant0)
      None).
pose {| states_pi:=x0::states_pi past_invariant0;
        sem_pi:=(uncurry
          (eq_rect_r (fun s1 => _ (_ s1)) (prod_action prod) e)
          (eq_rect _ (fun l => tuple (List.map _ l)) t _ (rev_append_rev_inverse symbol (prod_rhs prod))), sem_pi past_invariant0) |}.
rewrite H8.
apply (Cons_pstz start_sem _ _ semantics0 stack_top _ false _ p h).
rewrite <- H3.
unfold p, h, symbl_pi, symbl_hfi.
rewrite Heqo.
simpl.
rewrite e.
rewrite <- H10.
now reflexivity.
rewrite H5.
simpl.
rewrite e.
unfold eq_rect_r, sem_hfi, symbl_hfi.
rewrite Heqo.
revert e t H4 H9 p.
set ((rev_append_rev_inverse _ (prod_rhs prod))).
rewrite e.
injection x.
intros.
destruct H4.
replace t with (projT2 s0).
now reflexivity.
transitivity semantics.
apply JMeq_eq.
now apply (eq_ind (Some (existT _ (Some _) _)) (fun o => match o with Some e => _ ~= (projT2 e) | None => False end) JMeq_refl _ x).
apply JMeq_eq.
etransitivity.
now apply H2.
symmetry.
now apply H11.
now assumption.
now assumption.
now exact I.
Qed.

Lemma normalize_partial_semantic_tree:
  non_terminal_closed -> nullable_stable -> first_stable ->
  forall start_sem follow stack word n_steps,
    completeness_invariant start_sem follow stack word None false n_steps ->
    completeness_invariant start_sem follow stack word None true n_steps.
Proof.
intros.
dependent destruction H2.
destruct hole_future_invariant0.
destruct future_hfi0.
unfold symbl_hfi, word_future_hfi, future_hfi, hole_pseudo_hfi, hole_hfi, projT1, projT2 in *.
destruct hole_hfi0; [discriminate x|..].
clear sem_hfi0 symbl_hfi0 hole_pseudo_hfi0.
revert x0 t word_future_hfi0 future_sem_proof_hfi0 normalized_proof_hfi0 past_invariant0 pseudoprod0 stack_top word_top semantics H2 H3 H4 n_steps H5.
fix IH 4.
intros until future_sem_proof_hfi0.
case future_sem_proof_hfi0.
intros.
pose (Build_hole_future_invariant true
      (existT _ [] ()) I
      _ Nil_ptl
      None).
now apply (Cons_pstz _ _ _ semantics _ _ _ _ past_invariant0 h); assumption.
intros until p.
case p; intros.
pose (Build_hole_future_invariant true
        (existT _ (T t0::head_symbolsq) (sem, semantic_valuesq)) I
        _ (Cons_ptl _ _ _ (Terminal_pt t0 sem) _ _ _ p0)
        None).
now apply (Cons_pstz _ _ _ semantics _ _ _ _ past_invariant0 h); assumption.
rewrite <- app_assoc.
pose {| states_pi:=[]; sem_pi:= () |}.
change (stack_pi past_invariant0 stack_top) with (stack_pi p3 (stack_pi past_invariant0 stack_top)).
simpl.
rewrite <- Plus.plus_assoc.
apply (IH _ _ _ p1 I _ (Some p0) _ _ semantic_values).
now reflexivity.
now reflexivity.
apply (H _ _ _ _ H4).
now reflexivity.
destruct wordq as [] _eqn.
right.
split.
now reflexivity.
now apply (nullable_correct_list H0 _ _ _ eq_refl p2).
left.
clear H3.
rewrite <- Heql in p2.
destruct t0.
now apply (first_correct_list H0 H1 _ _ _ _ _ Heql p2).
pose (Build_hole_future_invariant false
        (existT _ head_symbolsq semantic_valuesq) I
        _ p2
        (Some (existT _ p0 semantic_values))).
now apply (Cons_pstz _ _ pseudoprod0 semantics _ _ _ _ past_invariant0 h); assumption.
Qed.

Lemma step_complete start_sem stack word buffer_end n_steps:
  complete ->
  completeness_invariant start_sem (projT1 (Streams.hd buffer_end)) stack 
                         word None false (S n_steps)->
  match step stack (word ++ buffer_end) with
    | OK Fail_sr => False
    | OK (Accept_sr sem b) => sem = start_sem /\ b = buffer_end /\ n_steps = 1
    | OK (Progress_sr stack_new buffer_new) =>
      exists word_new,
        word_new ++ buffer_end = buffer_new /\
        completeness_invariant start_sem (projT1 (Streams.hd buffer_end)) 
                               stack_new word_new None false n_steps
    | Err => True
  end.
Proof.
unfold complete.
intuition.
pose proof (normalize_partial_semantic_tree H8 H1 H _ _ _ _ _ H0).
clear H0 H H1 H8.
dependent destruction H7.
specialize (H2 _ _ _ _ H1).
specialize (H4 _ _ _ _ H1).
specialize (H5 _ _ _ _ H1).
simpl in H2, H4, H5.
revert semantics H0 H7.
unfold symbl_hfi, sem_hfi in *.
unfold hole_pseudo_hfi in x.
destruct (hole_hfi true hole_future_invariant0); [discriminate x|..].
generalize (future_sem_proof_hfi _ hole_future_invariant0).
generalize (projT2 (future_hfi true hole_future_invariant0)).
pose proof (normalized_proof_hfi _ hole_future_invariant0).
destruct (projT1 (future_hfi true hole_future_invariant0)); intros.
destruct t.
dependent destruction p.
destruct pseudoprod0; intuition.
assert (symbl_pi past_invariant0 = rev (prod_rhs p)).
simpl in H.
rewrite <- H.
rewrite <- rev_alt.
rewrite rev_involutive; reflexivity.
pose proof (reduce_complete _ _ _ _ _ _ _ _ H6 H1 H5 H7 H8).
unfold step.
revert p0 x.
rewrite <- x1.
intros.
dependent destruction x.
destruct (action_table (state_of_stack (stack_pi past_invariant0 stack_top))).
destruct d; intuition.
destruct H9.
destruct (reduce (stack_pi past_invariant0 stack_top) p); intuition.
now exists word_top; intuition.
replace (first_term_word word_top (projT1 (Streams.hd buffer_end))) 
with (projT1 (Streams.hd (([]++word_top) ++ buffer_end))) in H9.
destruct (Streams.hd (([]++word_top) ++ buffer_end)).
simpl in H9.
destruct (a x); intuition.
rewrite H9 in *.
destruct (reduce (stack_pi past_invariant0 stack_top) p0); intuition.
eexists.
now intuition.
now destruct word_top, buffer_end; reflexivity.
unfold step.
rewrite H5.
destruct past_invariant0.
unfold symbl_pi, stack_pi, states_pi, sem_pi in *.
destruct (extend_stack stack_top states_pi0 sem_pi0) as [] _eqn; intuition.
destruct s0; intuition.
destruct (compare_eqdec (last_symb_of_non_init_state state_cur) start_symbol); try exact I.
remember existT.
dependent destruction H8.
change (pseudoprod_rhs None) with [start_symbol] in *.
destruct (states_pi0); [discriminate H | ..].
destruct states_pi0.
unfold stack_pi, states_pi, sem_pi in Heqs.
dependent destruction Heqs.
split.
apply JMeq_eq.
rewrite Heqs0 in x3.
dependent destruction x3.
etransitivity.
now apply eq_rect_JMeq.
destruct sem_pi0.
dependent destruction x.
simpl in H7.
clear H H5.
revert s H1 H7.
unfold stack_pi.
simpl.
change (List.map last_symb_of_non_init_state [state_cur])
  with [last_symb_of_non_init_state state_cur].
rewrite e.
intros.
now apply (JMeq_ind (fun p => fst p ~= start_sem) (JMeq_refl (fst (start_sem, ()))) H7).
revert p0 x2.
rewrite <- x1.
intuition.
rewrite <- x2.
now reflexivity.
assert (length [start_symbol] =
         length (rev_append
           (List.map last_symb_of_non_init_state (n :: n0 :: states_pi0))
           [])).
rewrite H; intuition.
rewrite rev_append_rev in H8.
simpl in H8.
repeat rewrite app_length in H8.
repeat rewrite <- Plus.plus_assoc in H8.
simpl in H8.
now rewrite Plus.plus_comm in H8; intuition.
rewrite Heqs0 in x.
unfold hole_pseudo_hfi in x.
now destruct (hole_hfi false hole_future_invariant1); intuition.
destruct s; intuition.
unfold step.
destruct (action_table (state_of_stack (stack_pi past_invariant0 stack_top))); intuition.
dependent inversion p.
dependent destruction p0. 
unfold app, app_str, Streams.hd.
destruct (a t0); intuition.
exists (wordq++word_top)%list.
intuition.
pose (Build_hole_future_invariant false
      (existT _ _ _) I
      _ p1
      None).
pose {| states_pi:=s::states_pi past_invariant0;
        sem_pi:=(eq_rect_r (fun s => _ s) semantic_valuet0 e, sem_pi past_invariant0) |}.
assert (rev_append (symbl_pi p0) (symbl_hfi false h) = pseudoprod_rhs pseudoprod0).
simpl.
now rewrite e; intuition.
simpl.
clear H12.
revert semantic_valuet0 t p H9 p0 H13 H7.
rewrite <- e.
intros.
dependent destruction H9.
now apply (Cons_pstz start_sem _ pseudoprod0 semantics stack_top word_top false _ p0 h); intuition.
Qed.

Theorem parse_complete word buffer_end n_steps sem:
  complete ->
  forall tree:parse_tree start_symbol word sem,
  match parse (word ++ buffer_end) n_steps with
    | OK (Parsed_pr sem_res buffer_end_res) =>
      sem_res = sem /\ buffer_end_res = buffer_end /\ 
      n_steps >= parse_tree_size tree+2
    | OK Fail_pr => False
    | OK Timeout_pr => n_steps < parse_tree_size tree+2
    | Err => True
  end.
Proof.
intros.
assert (completeness_invariant sem (projT1 (Streams.hd buffer_end)) Nil_stack word None false (S (parse_tree_size tree + 1 + 1))).
unfold complete in H.
intuition.
pose (Cons_ptl _ _ _ tree _ _ _  Nil_ptl).
pose (Build_hole_future_invariant false (existT _ _ _) I _ p None).
pose proof (Cons_pstz sem (projT1 (Streams.hd buffer_end)) None _ Nil_stack [] false _ {| states_pi:=[]; sem_pi:=() |} h eq_refl JMeq_refl (H2 _) (Nil_pstz _ _)).
simpl in H6.
repeat rewrite <- app_nil_end in H6.
exact H6.
revert H0.
unfold parse.
rewrite <- Plus.plus_assoc; simpl.
generalize (parse_tree_size tree + 2).
clear tree.
intro.
revert word n_steps.
generalize Nil_stack.
induction n; simpl; intuition.
dependent destruction H0.
destruct n_steps0; intuition.
now dependent destruction H3.
destruct n_steps; simpl; intuition.
pose proof (step_complete _ _ _ buffer_end _ H H0).
destruct (step s (app_str word buffer_end)); intuition.
destruct s0; simpl; intuition.
destruct H1.
rewrite <- (proj1 H1).
pose proof (IHn s0 x n_steps (proj2 H1)).
unfold token in H2.
destruct (parse_fix s0 (x ++ buffer_end) n_steps); intuition.
destruct p; intuition.
Qed.

End Make.
