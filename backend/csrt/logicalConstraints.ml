type t = LC of IndexTerms.t

let pp atomic (LC c) = IndexTerms.pp atomic c

let subst_var subst (LC c) = 
  LC (IndexTerms.subst_var subst c)

let subst_vars = Tools.make_substs subst_var

let concretise_field subst (LC c) = 
  LC (IndexTerms.concretise_field subst c)

let vars_in (LC c) = IndexTerms.vars_in c
