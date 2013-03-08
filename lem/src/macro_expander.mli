open Types
open Typed_ast

type level = 
  | Top_level
  | Nested

type pat_pos = 
  | Bind
  | Param

type pat_position = level * pat_pos

module Expander(C : Exp_context) : sig
  val expand_defs :
    def list -> ((exp -> exp option) * (pat_position -> pat -> pat option)) -> def list

  (* The first argument is true if the pattern is part of a top-level definition
  * and false otherwise.  This value is given as the first argument to eacn
  * macro *)
  val expand_pat : pat_position -> pat -> (pat_position -> pat -> pat option) -> pat

  val expand_exp : ((exp -> exp option) * (pat_position -> pat -> pat option)) -> exp -> exp
end

val list_to_mac : ('b -> 'c option) list -> 'b -> 'c option
val list_to_bool_mac : (pat_position -> 'b -> 'c option) list -> pat_position -> 'b -> 'c option

