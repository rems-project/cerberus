type t = IndexTerms.t

let pp c = Pp.dquotes (IndexTerms.pp c)

let json c : Yojson.Safe.t = 
  IndexTerms.json c


let subst_var substitution c = 
  IndexTerms.subst_var substitution c

let subst_it substitution c = 
  IndexTerms.subst_it substitution c


let subst_vars c = Subst.make_substs subst_var c
let subst_its c = Subst.make_substs subst_it c

let free_vars c = IndexTerms.free_vars c

let equal c c' = IndexTerms.equal c c'









