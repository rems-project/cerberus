open PPrint
open List


type t = (VarTypes.t Binders.t) list

let pp ts = flow_map (comma ^^ break 1) (Binders.pp VarTypes.pp) ts

let subst sym with_sym bs = 
  map (Binders.subst VarTypes.subst sym with_sym) bs

let names t = List.map (fun {Binders.name; _} -> name) t

let rename newname t = 
  match t with
  | [] -> print_endline "\n\nempty return type\n\n"; []
  | {Binders.name; _} :: _ -> subst name newname t



