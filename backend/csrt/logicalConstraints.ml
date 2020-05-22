type t = LC of IndexTerms.t

let pp atomic (LC c) = IndexTerms.pp atomic c

let subst_var sym with_it (LC c) = 
  LC (IndexTerms.subst_var sym with_it c)

let concretise_field id with_it (LC c) = 
  LC (IndexTerms.concretise_field id with_it c)

let vars_in (LC c) = IndexTerms.vars_in c
