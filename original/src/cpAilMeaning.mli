type t
type func

val none : t
val empty : t

val conj : t -> t -> t
val conj_seq_before : t -> t -> t
val disj : t -> t -> t

val add_constraint : t -> CpAilConstraint.constr -> t
val add_constraint_set : t -> CpAilConstraint.t -> t
val add_action : t -> CpAilAction.t -> t

val break    : t -> func
val continue : t -> func
val normal   : t -> func
val return   : t -> func

val empty_func : func
val flatten_func : func -> t

val enter_loop : t -> t -> func -> func
val exit_loop : t -> func -> func

val conj_seq_before_func : func -> func -> func
val disj_func : func -> func -> func

val add_constraint_func : func -> CpAilConstraint.constr -> func
val add_action_func : func -> CpAilAction.t -> func
val add_action_entire_func : func -> CpAilAction.t -> func
val add_actions_entire_func_sb : func -> CpAilAction.t BatSet.t -> func

module Operators : sig
  val (<&>) : t -> t -> t
  val (&>>) : t -> t -> t
  val (<|>) : t -> t -> t
  val (<&-) : t -> CpAilConstraint.constr -> t
  val (<@-) : t -> CpAilAction.t -> t
end

module StatementOperators : sig
  val (&>>) : func -> func -> func
  val (<|>) : func -> func -> func
  val (<&-) : func -> CpAilConstraint.constr -> func
  val (<@-) : func -> CpAilAction.t -> func
end

module Print : sig
  val pp : t -> Pprint.document
end

module Solve : sig
  val simplify_result : t CpAil.result -> (CpAilConstraint.t BatSet.t) CpAil.result
end

module Graph : sig
  val dot_result : string -> t CpAil.result -> unit
end





