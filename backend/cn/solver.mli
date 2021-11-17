type solver
type model
type model_with_q = model * (Sym.t * LogicalSorts.t) option


val init : unit -> unit

val push : unit -> unit
val pop : unit -> unit
val add : Global.t -> LogicalConstraints.t -> unit


val provable : shortcut_false:bool -> Global.t -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]


val model : unit -> model_with_q



val eval : Memory.struct_decls -> model -> IndexTerms.t -> IndexTerms.t option
