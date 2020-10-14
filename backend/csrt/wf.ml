type error = 
  | Unbound_name of Sym.t
  | Unconstrained_lvar of Sym.t
