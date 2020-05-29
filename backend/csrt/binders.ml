open Pp

type 'bound t = {name : Sym.t; bound: 'bound}

let pp atomic pp_bound {name;bound} = 
  let mparens pped = if atomic then parens pped else pped in
  mparens (typ (Sym.pp name) (pp_bound bound))

let pps pp_name pp_bound = 
  pp_list (pp false pp_bound)

let subst bound_subst subst b = 
  { name = Sym.subst subst b.name;
    bound = bound_subst subst b.bound }

let substs name_subst bound_subst = 
  Tools.make_substs (subst bound_subst)



let subst_list name_subst bound_subst substitution bs = 
  List.map (subst bound_subst substitution) bs

let to_tuple {name;bound} = (name,bound)
let from_tuple (name,bound) = {name;bound}
