open Automaton
open Datatypes
open Streams
open Tuples
open Validator_safe

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
  
  (** val symb_stack_of_stack : Inter.stack -> A.Gram.symbol list **)
  
  let rec symb_stack_of_stack = function
  | Inter.Nil_stack -> []
  | Inter.Cons_stack (s, s0, q) ->
    (A.last_symb_of_non_init_state s)::(symb_stack_of_stack q)
  
  (** val state_stack_of_stack : Inter.stack -> (A.state -> bool) list **)
  
  let rec state_stack_of_stack = function
  | Inter.Nil_stack -> (Valid.singleton_state_pred A.Init)::[]
  | Inter.Cons_stack (s, s0, q) ->
    (Valid.singleton_state_pred (A.Ninit s))::(state_stack_of_stack q)
  
  (** val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
  
  let eq_rew_dep x f y =
    f
  
  (** val parse_with_safe :
      A.GramDefs.token coq_Stream -> nat -> Inter.parse_result **)
  
  let parse_with_safe buffer n_steps =
    let r = Inter.parse buffer n_steps in
    (match r with
     | Inter.Err -> assert false (* absurd case *)
     | Inter.OK p -> p)
 end

