open Pp_tools


type ('name, 'bound) t = {name : 'name; bound: 'bound}

let pp pp_name pp_bound {name;bound} = 
  PPrint.parens (typ (pp_name name) (pp_bound bound))

let pps pp_name pp_bound = 
  Pp_tools.pp_list None (pp pp_name pp_bound)

let subst name_subst bound_subst subst b = 
  { name = name_subst subst b.name;
    bound = bound_subst subst b.bound }

let substs name_subst bound_subst = 
  Tools.make_substs (subst name_subst bound_subst)



let subst_list name_subst bound_subst substitution bs = 
  List.map (subst name_subst bound_subst substitution) bs

let to_tuple {name;bound} = (name,bound)
let from_tuple (name,bound) = {name;bound}
