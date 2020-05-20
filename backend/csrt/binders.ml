open Pp_tools


type ('name, 'bound) t = {name : 'name; bound: 'bound}

let pp pp_name pp_bound {name;bound} = 
  PPrint.parens (typ (pp_name name) (pp_bound bound))

let pps pp_name pp_bound = 
  Pp_tools.pp_list None (pp pp_name pp_bound)

let subst name_subst bound_subst sym with_it b = 
  { name = name_subst sym with_it b.name;
    bound = bound_subst sym with_it b.bound }

let subst_list name_subst bound_subst sym with_it bs = 
  List.map (subst name_subst bound_subst sym with_it) bs

let to_tuple {name;bound} = (name,bound)
let from_tuple (name,bound) = {name;bound}
