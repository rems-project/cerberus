open Automaton
open Datatypes
open Streams
open Tuples

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
  (** val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let eq_rew_r_dep x y hC =
    hC
 end

