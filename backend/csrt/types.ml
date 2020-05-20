open PPrint
open List


type t = ((Sym.t, VarTypes.t) Binders.t) list

let pp ts = flow_map (comma ^^ break 1) (Binders.pp Sym.pp VarTypes.pp) ts

let subst_var sym with_sym bs = 
  Binders.subst_list Sym.subst VarTypes.subst_var sym with_sym bs

let concretise_field id with_it t = 
 match t with
 | VarTypes.C t -> 
    VarTypes.C (LogicalConstraints.concretise_field id with_it t)
 | _ -> t

let names t = List.map (fun {Binders.name; _} -> name) t

let rename newname t = 
  match t with
  | [] -> print_endline "\n\nempty return type\n\n"; []
  | {Binders.name; _} :: _ -> subst_var name newname t



