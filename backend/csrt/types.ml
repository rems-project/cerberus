open PPrint
open List


type t = Binders.t list

let pp ts = flow_map (space ^^ comma ^^ break 1) Binders.pp ts

let subst sym with_sym bs = 
  map (Binders.subst sym with_sym) bs

let names t = List.map (fun {Binders.name; _} -> name) t

let rename newname t = 
  match t with
  | [] -> print_endline "\n\nempty return type\n\n"; []
  | {Binders.name; _} :: _ -> subst name newname t



