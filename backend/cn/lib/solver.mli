(* Module Solver -- Interface to the SMT solver via SMTLIB *)
type solver

type model

(* (TODO: BCP: The "with quantifiers" part will be the instantiations that the solver
   found -- is that right?) *)
type model_with_q = model * (Sym.t * LogicalSorts.t) list

val empty_model : model

(* Global flags to pass to the solver (TODO: BCP: Could use a bit more documentation,
   maybe) *)
val random_seed : int ref

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

(* TODO: BCP: What is this? *)
val num_scopes : solver -> int

(* Run the solver. Note that we pass the assumptions explicitly even though they are also
   available in the solver context, because CN is going some simplification on its own. *)
val provable
  :  loc:Locations.t ->
  solver:solver ->
  global:Global.t ->
  assumptions:Context.LCSet.t ->
  simp_ctxt:Simplify.simp_ctxt ->
  LogicalConstraints.t ->
  [> `True | `False ]

(* Ask the solver for the model that it found in a call to [provable] *)
val model : unit -> model_with_q

(* Ask the solver to evaluate a CN term in the context of a model. (Might return None in
   case we ask for the value of a "don't care" value in the (minimal) model.) *)
(* TODO: BCP: I don't understand how this could ever be called -- how do we get a model to
   pass it??? *)
val eval
  :  Global.t ->
  (* TODO: BCP: IIUC Christopher thinks this is not needed? *)
  model ->
  IndexTerms.t ->
  IndexTerms.t option

(* TODO: BCP: What is this? *)
val set_slow_smt_settings : float option -> string option -> unit

(* Debugging *)
(* TODO: BCP: This one seems misnamed -- it doesn't return a string...? *)
val debug_solver_to_string : solver -> unit

val debug_solver_query
  :  solver ->
  Global.t ->
  Context.LCSet.t ->
  IndexTerms.t list ->
  LogicalConstraints.t ->
  unit

(* CHT *)
val ask_solver : Global.t -> LogicalConstraints.logical_constraint list -> Simple_smt.result