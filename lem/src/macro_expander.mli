open Types
open Typed_ast

module Expander(C : Exp_context) : sig
  val expand_defs :
    def list -> ((exp -> exp option) * (bool -> pat -> pat option)) -> def list

  (* The first argument is true if the pattern is part of a top-level definition
  * and false otherwise.  This value is given as the first argument to eacn
  * macro *)
  val expand_pat : bool -> pat -> (bool -> pat -> pat option) -> pat

  val expand_exp : ((exp -> exp option) * (bool -> pat -> pat option)) -> exp -> exp
end

val list_to_mac : ('b -> 'c option) list -> 'b -> 'c option
val list_to_bool_mac : (bool -> 'b -> 'c option) list -> bool -> 'b -> 'c option

