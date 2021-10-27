type context
type solver
type expr
type sort
type model


val context : context


val sort : Memory.struct_decls -> BaseTypes.t -> sort
val term : Memory.struct_decls -> IndexTerms.t -> expr
val lambda : Memory.struct_decls -> (Sym.t * BaseTypes.t) -> IndexTerms.t -> expr
val constr : Global.t -> LogicalConstraints.t -> expr option

val z3_sort : sort -> BaseTypes.t
val z3_expr : Memory.struct_decls -> expr -> IndexTerms.t option


val provable : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]
val provable_or_model : Global.t -> solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False of model]


val push : solver -> unit
val pop : solver -> unit
val new_solver : unit -> solver
val add : solver -> expr list -> unit
val eval : model -> expr -> expr option
