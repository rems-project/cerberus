type solver
type model
type model_with_q = model * (Sym.t * LogicalSorts.t) list

val random_seed : int ref
val log_to_temp : bool ref

val make : Global.t -> solver

val num_scopes : solver -> int
val push : solver -> unit
val pop : solver -> int -> unit
val add_assumption : solver -> Global.t -> LogicalConstraints.t -> unit

val set_slow_smt_settings : float option -> string option -> unit


val provable :
  loc:Locations.t ->
  solver:solver ->
  global:Global.t ->
  assumptions:Context.LCSet.t ->
  simp_ctxt:Simplify.simp_ctxt ->
  pointer_facts:IndexTerms.t list ->
  LogicalConstraints.t ->
  [> `True | `False ]


val model :
  unit ->
  model_with_q



val eval :
  Global.t ->
  model ->
  IndexTerms.t ->
  IndexTerms.t option


val get_solver_focused_terms : solver ->
  assumptions:Context.LCSet.t ->
  pointer_facts:IndexTerms.t list ->
  Global.t -> (IndexTerms.t_bindings * IndexTerms.t) list

val debug_solver_to_string : solver -> unit

val debug_solver_query : solver -> Global.t -> Context.LCSet.t ->
  IndexTerms.t list -> LogicalConstraints.t -> unit

