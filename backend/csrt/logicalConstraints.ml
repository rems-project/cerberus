type t = LC of IndexTerms.t

let pp (LC c) = IndexTerms.pp c

let subst sym with_it (LC c) = 
  LC (IndexTerms.subst sym with_it c)

let subst_named sym with_it (name, LC c) = 
  (Sym.subst name sym with_it, LC (IndexTerms.subst sym with_it c))

let subst_nameds sym with_it = List.map (subst_named sym with_it)


let syms_in (LC c) = IndexTerms.syms_in c


