open Pp_tools


type 'bound t = {name: Sym.t; bound: 'bound}

let pp pp_bound {name;bound} = 
  PPrint.parens (typ (Sym.pp name) (pp_bound bound))

let pps pp_bound = 
  Pp_tools.pp_list None (pp pp_bound)

let subst bound_subst sym with_it b = 
  { name = Sym.subst sym with_it b.name;
    bound = bound_subst sym with_it b.bound }

let subst_list bound_subst sym with_it bs = 
  List.map (subst bound_subst sym with_it) bs

let to_tuple {name;bound} = (name,bound)
let from_tuple (name,bound) = {name;bound}
