type t = LC of IndexTerms.t

let pp (LC c) = Pp.dquotes (IndexTerms.pp c)

let json (LC c) : Yojson.Safe.t = 
  IndexTerms.json c


let subst_var substitution (LC c) = 
  LC (IndexTerms.subst_var substitution c)

let subst_it substitution (LC c) = 
  LC (IndexTerms.subst_it substitution c)


let subst_vars = Subst.make_substs subst_var
let subst_its = Subst.make_substs subst_it

let vars_in (LC c) = IndexTerms.vars_in c

let equal (LC c) (LC c') = IndexTerms.equal c c'

let negate (LC c) = LC (Not c)


let index_term (LC c) = c


let unpack (LC c) = c






