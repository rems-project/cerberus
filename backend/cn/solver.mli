(* Module Solver -- Interface to the SMT solver via SMTLIB *)

type solver

type model

val empty_model : model

type model_with_q = model * (Sym.t * LogicalSorts.t) list
(* The "with quantifiers" part will be the instantiations that the
   solver found.  To implement provable (Forall ((s,bt), t)), CN picks
   a fresh variable s' and checks that not t[s'/s] is
   unsatisfiable ("there exists no choice of s such that t doesn't
   hold"). If provable returns false, i.e. the SMT solver found an s'
   for which t[s'/s] doesn't hold, then model_with_q has that s' for
   its second component. *)

(* Global flags to pass to the solver *)

val random_seed : int ref

val log_to_temp : bool ref

val log_dir : string option ref

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

val num_scopes : solver -> int

(* Run the solver.  Note that we pass the assumptions explicitly even
   though they are also available in the solver context, because CN is
   going some simplification on its own.  Plus we have a default
   quantifier instantiation heuristic, which adds additional
   constraints derived from assumptions based on the to-be-proved
   constraint. *)
val provable
  :  loc:Locations.t ->
  solver:solver ->
  global:Global.t ->
  assumptions:Context.LCSet.t ->
  simp_ctxt:Simplify.simp_ctxt ->
  LogicalConstraints.t ->
  [> `True | `False ]

(* Ask the solver for the model that it found in a call to [provable] *)
(* TODO: BCP: This should be renamed (confusing) *)
val model : unit -> model_with_q

(* Ask the solver to evaluate a CN term in the context of a
   model.  (Might return None in case we ask for the value of a "don't
   care" value in the (minimal) model.) *)
val eval
  :  Global.t ->
  (* TODO: BCP: IIUC Christopher thinks this is not needed? *)
  model ->
  IndexTerms.t ->
  IndexTerms.t option
(* TODO: CP: Here and in other places in the solver module, I think,
   the global argument can be removed: the solver is initialised with
   a global typing context at some point earlier on, and then this is
   expected not to change any longer. *)

(* For logging slow-running SMT queries (TODO: BCP: CP says maybe this
   is not needed any more... I see that it is called from Main, but
   possibly it could be removed?) *)
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
