type solver
type model


val provable : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]
val provable_or_model : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False of model]


val push : solver -> unit
val pop : solver -> unit
val make : unit -> solver
val add : Global.t -> solver -> LogicalConstraints.t -> unit

val eval : Memory.struct_decls -> model -> IndexTerms.t -> IndexTerms.t option
