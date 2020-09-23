module IT=IndexTerms

type t = LC of IT.t

let pp atomic (LC c) = IT.pp atomic c

let subst_var substitution (LC c) = LC (IT.subst_var substitution c)
let subst_vars = Subst.make_substs subst_var

let instantiate_struct_member subst (LC c) = 
  LC (IT.instantiate_struct_member subst c)

let vars_in (LC c) = IT.vars_in c

let equal (LC c) (LC c') = IT.equal c c'
