type solver
type model


val make : unit -> solver

val push : solver -> unit
val pop : solver -> unit
val add : Global.t -> solver -> LogicalConstraints.t -> unit


val provable : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]
val provable_or_model : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False of model]



val eval : Memory.struct_decls -> model -> IndexTerms.t -> IndexTerms.t option
