val sort : Memory.struct_decls -> BaseTypes.t -> Z3.Sort.sort
val provable : Memory.struct_decls -> Z3.Solver.solver -> LogicalConstraints.t -> bool
val model : Z3.Solver.solver -> Z3.Model.model
val term : Memory.struct_decls -> IndexTerms.t -> Z3.Expr.expr
val lambda : Memory.struct_decls -> (Sym.t * BaseTypes.t) -> IndexTerms.t -> Z3.Expr.expr
val constr : Memory.struct_decls -> LogicalConstraints.t -> Z3.Expr.expr list

val z3_sort : Z3.Sort.sort -> BaseTypes.t
val z3_expr : Memory.struct_decls -> Z3.Expr.expr -> IndexTerms.t option


val context : Z3.context
