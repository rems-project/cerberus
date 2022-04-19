type solver
type model
type model_with_q = model * (Sym.t * LogicalSorts.t) list


val make : Memory.struct_decls -> solver

val push : solver -> unit
val pop : solver -> unit
val add_assumption : solver -> Global.t -> LogicalConstraints.t -> unit


val provable : 
  loc:Locations.t ->
  solver:solver -> 
  global:Global.t -> 
  trace_length:int ->
  assumptions:Context.LCSet.t -> 
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
