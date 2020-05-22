open List
module Loc=Locations
module SymSet = Set.Make(Sym)
(* open PPrint *)
(* open Pp_tools *)





type t = 
  | Base of BaseTypes.t
                      

let pp atomic = function
  | Base bt -> BaseTypes.pp atomic bt

let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst_var sym with_it ls =
  match ls with
  | Base bt -> Base (BaseTypes.subst_var sym with_it bt)


let vars_in = function
  | Base bt -> BaseTypes.vars_in bt

