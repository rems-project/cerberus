open BaseTypes
module IT = IndexTerms
module SMT = Simple_smt

type solver
val push: solver -> unit
val pop: solver -> int -> unit
val declare_var: solver -> Sym.t -> basetype -> unit

val make : Global.t -> solver




val translate_term:        solver -> IT.t -> SMT.sexp
val get_ivalue: basetype -> SMT.sexp -> IT.t
