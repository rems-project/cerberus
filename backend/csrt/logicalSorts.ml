open List
module Loc=Locations
module SymSet = Set.Make(Sym)
(* open PPrint *)
(* open Pp_tools *)





type t = 
  | Base of BaseTypes.t
                      

let pp atomic = function
  | Base bt -> BaseTypes.pp atomic bt

let equal t1 t2 = t1 = t2

let equals ts1 ts2 = 
  List.length ts1 = List.length ts2 &&
  for_all (fun (t1,t2) -> equal t1 t2) (combine ts1 ts2)

