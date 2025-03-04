(* Module Solver -- Interface to the SMT solver via SMTLIB *)
type solver

type model

(** Model with quantifier instantiations *)
type model_with_q = model * (Sym.t * BaseTypes.t) list

val empty_model : model

module Logger : sig
  val to_file : bool ref

  val dir : string option ref
end

val solver_path : string option ref

val solver_flags : string list option ref

val solver_type : Simple_smt.solver_extensions option ref

(* Create a solver *)
val make : Global.t -> solver

(* Incrementally (and imperatively) add an assumption to the solver state *)
val add_assumption : solver -> Global.t -> LogicalConstraints.t -> unit

(* Save / restore solver state, to support backtracking *)
val push : solver -> unit

val pop : solver -> int -> unit

(** Number of scopes in the solver. Currently only used by [Typing.sandbox],
    but may be unnecessary https://github.com/rems-project/cerberus/issues/752 *)
val num_scopes : solver -> int

(* Resets internal state for the model evaluator *)
val reset_model_evaluator_state : unit -> unit

(* Run the solver. Note that we pass the assumptions explicitly even though they are also
   available in the solver context, because CN is going some simplification on its own. *)
val provableWithUnknown
  :  loc:Locations.t ->
  solver:solver ->
  assumptions:LogicalConstraints.Set.t ->
  simp_ctxt:Simplify.simp_ctxt ->
  LogicalConstraints.t ->
  [> `True | `False | `Unknown ]
(*TODO CHT*)

(* Run the solver. Note that we pass the assumptions explicitly even though they are also
   available in the solver context, because CN is going some simplification on its own. *)
val provable
  :  loc:Locations.t ->
  solver:solver ->
  assumptions:LogicalConstraints.Set.t ->
  simp_ctxt:Simplify.simp_ctxt ->
  LogicalConstraints.t ->
  [> `True | `False ]

(* Ask the solver for the model that it found in a call to [provable] *)
val model : unit -> model_with_q

(** Ask the solver to evaluate a CN term in the context of an already obtained
    counter-example model (e.g. for evaluating sub-terms). Might return None in
    case we ask for the value of a "don't care" value in the (minimal) model. *)
val eval : model -> IndexTerms.t -> IndexTerms.t option

(** Try undecidable SMT solving using full set of assumptions. *)
val try_hard : bool ref
