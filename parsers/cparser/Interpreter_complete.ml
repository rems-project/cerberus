open Alphabet
open Automaton
open Datatypes
open Int0
open List0
open Specif
open Streams
open Tuples
open Validator_complete

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Make = 
 functor (A:T) ->
 functor (Inter:sig 
  type 'a result =
    | Err
    | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 : ('a1*'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream
  
  type stack =
    | Nil_stack
    | Cons_stack of A.noninitstate * A.Gram.symbol_semantic_type * stack
  
  val stack_rect :
    'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1 ->
    'a1) -> stack -> 'a1
  
  val stack_rec :
    'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1 ->
    'a1) -> stack -> 'a1
  
  val state_of_stack : stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> A.Gram.symbol list -> tuple ->
    (stack*tuple) result
  
  val reduce : stack -> A.Gram.production -> stack result
  
  type step_result =
    | Fail_sr
    | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
    | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  val step_result_rect :
    'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
    'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
    'a1
  
  val step_result_rec :
    'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
    'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
    'a1
  
  val step : stack -> A.GramDefs.token coq_Stream -> step_result result
  
  type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  val parse_result_rect :
    'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream
    -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream
    -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    stack -> A.GramDefs.token coq_Stream -> nat -> parse_result result
  
  val parse : A.GramDefs.token coq_Stream -> nat -> parse_result result
 end) ->
 struct 
  module Valid = Make(A)
  
  (** val first_term_word :
      A.GramDefs.token list -> A.Gram.terminal -> A.Gram.terminal **)
  
  let first_term_word word follow =
    match word with
      | [] -> follow
      | t0::l -> let Coq_existT (t1, s) = t0 in t1
  
  (** val extend_stack :
      Inter.stack -> A.noninitstate list -> __ -> Inter.stack **)
  
  let rec extend_stack stack_cur states x =
    match states with
      | [] -> stack_cur
      | t0::q ->
          let semt,semq = Obj.magic x in
          Inter.Cons_stack (t0, semt, (extend_stack stack_cur q semq))
  
  type past_invariant = { states_pi : A.noninitstate list; sem_pi : tuple }
  
  (** val past_invariant_rect :
      (A.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1 **)
  
  let past_invariant_rect f p =
    let { states_pi = x; sem_pi = x0 } = p in f x x0
  
  (** val past_invariant_rec :
      (A.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1 **)
  
  let past_invariant_rec f p =
    let { states_pi = x; sem_pi = x0 } = p in f x x0
  
  (** val states_pi : past_invariant -> A.noninitstate list **)
  
  let states_pi p =
    p.states_pi
  
  (** val symbl_pi : past_invariant -> A.Gram.symbol list **)
  
  let symbl_pi p =
    List0.map A.last_symb_of_non_init_state (states_pi p)
  
  (** val sem_pi : past_invariant -> tuple **)
  
  let sem_pi p =
    p.sem_pi
  
  (** val stack_pi : past_invariant -> Inter.stack -> Inter.stack **)
  
  let stack_pi p stack_top =
    extend_stack stack_top (states_pi p) (sem_pi p)
  
  type hole_future_invariant = { future_hfi : (A.Gram.symbol list, tuple)
                                              sigT;
                                 word_future_hfi : 
                                 A.GramDefs.token list;
                                 future_sem_proof_hfi : 
                                 A.GramDefs.parse_tree_list;
                                 hole_hfi : (A.Gram.production, tuple) sigT
                                            option }
  
  (** val hole_future_invariant_rect :
      bool -> ((A.Gram.symbol list, tuple) sigT -> __ -> A.GramDefs.token
      list -> A.GramDefs.parse_tree_list -> (A.Gram.production, tuple) sigT
      option -> 'a1) -> hole_future_invariant -> 'a1 **)
  
  let hole_future_invariant_rect normalized f h =
    let { future_hfi = x; word_future_hfi = x0; future_sem_proof_hfi = x1;
      hole_hfi = x2 } = h
    in
    f x __ x0 x1 x2
  
  (** val hole_future_invariant_rec :
      bool -> ((A.Gram.symbol list, tuple) sigT -> __ -> A.GramDefs.token
      list -> A.GramDefs.parse_tree_list -> (A.Gram.production, tuple) sigT
      option -> 'a1) -> hole_future_invariant -> 'a1 **)
  
  let hole_future_invariant_rec normalized f h =
    let { future_hfi = x; word_future_hfi = x0; future_sem_proof_hfi = x1;
      hole_hfi = x2 } = h
    in
    f x __ x0 x1 x2
  
  (** val future_hfi :
      bool -> hole_future_invariant -> (A.Gram.symbol list, tuple) sigT **)
  
  let future_hfi normalized h =
    h.future_hfi
  
  (** val word_future_hfi :
      bool -> hole_future_invariant -> A.GramDefs.token list **)
  
  let word_future_hfi normalized h =
    h.word_future_hfi
  
  (** val future_sem_proof_hfi :
      bool -> hole_future_invariant -> A.GramDefs.parse_tree_list **)
  
  let future_sem_proof_hfi normalized h =
    h.future_sem_proof_hfi
  
  (** val hole_hfi :
      bool -> hole_future_invariant -> (A.Gram.production, tuple) sigT option **)
  
  let hole_hfi normalized h =
    h.hole_hfi
  
  (** val hole_pseudo_hfi :
      bool -> hole_future_invariant -> (A.Gram.production option, tuple) sigT
      option **)
  
  let hole_pseudo_hfi normalized h =
    match hole_hfi normalized h with
      | Some i -> Some (Coq_existT ((Some (projT1 i)), (projT2 i)))
      | None -> None
  
  (** val symbl_hfi : bool -> hole_future_invariant -> A.Gram.symbol list **)
  
  let symbl_hfi normalized h =
    match hole_hfi normalized h with
      | Some i -> (A.Gram.NT
          (A.Gram.prod_lhs (projT1 i)))::(projT1 (future_hfi normalized h))
      | None -> projT1 (future_hfi normalized h)
  
  (** val sem_hfi : bool -> hole_future_invariant -> tuple **)
  
  let sem_hfi normalized h =
    match hole_hfi normalized h with
      | Some i ->
          Obj.magic
            ((uncurry (List0.map (Obj.magic __) (A.Gram.prod_rhs (projT1 i)))
               (A.Gram.prod_action (projT1 i)) (projT2 i)),
            (projT2 (future_hfi normalized h)))
      | None -> projT2 (future_hfi normalized h)
  
  (** val coq_JMeq_rew_r : 'a1 -> 'a2 -> 'a3 -> 'a3 **)
  
  let coq_JMeq_rew_r x b hC =
    hC
  
  (** val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let eq_rew_r_dep x y hC =
    hC
  
  (** val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
  
  let eq_rew_dep x f y =
    f
 end

