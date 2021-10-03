val sort : Memory.struct_decls -> BaseTypes.t -> Z3.Sort.sort
val provable : Global.t -> Z3.Solver.solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False ]
val provable_or_model : Global.t -> Z3.Solver.solver -> LogicalConstraints.t list -> LogicalConstraints.t -> [> `True | `False of Z3.Model.model]
val term : Memory.struct_decls -> IndexTerms.t -> Z3.Expr.expr
val lambda : Memory.struct_decls -> (Sym.t * BaseTypes.t) -> IndexTerms.t -> Z3.Expr.expr
val constr : Global.t -> LogicalConstraints.t -> Z3.Expr.expr option

val z3_sort : Z3.Sort.sort -> BaseTypes.t
val z3_expr : Memory.struct_decls -> Z3.Expr.expr -> IndexTerms.t option


val context : Z3.context

val simp : Memory.struct_decls -> IndexTerms.t -> IndexTerms.t option
