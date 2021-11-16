type solver
type model
type model_with_q = model * (Sym.t * LogicalSorts.t) option


val make : unit -> solver

val push : solver -> unit
val pop : solver -> unit
val add : Global.t -> solver -> LogicalConstraints.t -> unit


val provable : shortcut_false:bool -> Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]
val provable_or_model : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False of model_with_q]



val eval : Memory.struct_decls -> model -> IndexTerms.t -> IndexTerms.t option
