open Pp
module RT = ReturnTypes
module SymSet = Set.Make(Sym)


type t = False


let subst_var substitution = function
  | False -> False

let subst_it substitution = function
  | False -> False

let instantiate_struct_member substitution = function
  | False -> False

let free_vars = function
  | False -> SymSet.empty

let pp = function
  | False -> if !unicode then !^"\u{22A5}" else !^"false"

(* let closed (_bound : SymSet.t) = function
 *   | False -> Resultat.return () *)
