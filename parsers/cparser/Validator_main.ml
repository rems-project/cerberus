open Alphabet
open Automaton
open Datatypes
open Int0
open Interpreter
open Interpreter_complete
open Interpreter_correct
open Interpreter_safe
open Specif
open Streams
open Tuples

type __ = Obj.t

module Make = 
 functor (Aut:Automaton.T) ->
 struct 
  module Inter = Interpreter.Make(Aut)
  
  module Safe = Make(Aut)(Inter)
  
  module Correct = Interpreter_correct.Make(Aut)(Inter)
  
  module Complete = Interpreter_complete.Make(Aut)(Inter)
  
  (** val complete_validator : bool **)
  
  let complete_validator =
    Complete.Valid.is_complete
  
  (** val safe_validator : bool **)
  
  let safe_validator =
    Safe.Valid.is_safe
  
  (** val parse :
      nat -> Aut.GramDefs.token coq_Stream -> Inter.parse_result **)
  
  let parse n_steps buffer =
    Safe.parse_with_safe buffer n_steps
 end

