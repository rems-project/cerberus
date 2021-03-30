module IT = IndexTerms
module SymSet = Set.Make(Sym)

type entry = IndexTerms.t

let subst_it_entry substitution it = 
  IT.subst_it substitution it

let subst_var_entry substitution it = 
  IT.subst_var substitution it
  
let pp_entry it = 
  IT.pp it


type t = entry list

let subst_it substitution assignment = 
  List.map (subst_it_entry substitution) assignment

let subst_var substitution assignment = 
  List.map (subst_var_entry substitution) assignment


let subst_its substs assignment = 
  Subst.make_substs subst_it substs assignment


let subst_vars substs assignment = 
  Subst.make_substs subst_var substs assignment


let pp assignment =
  Pp.list pp_entry assignment
