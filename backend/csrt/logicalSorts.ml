open List
module Loc=Location

type t = 
  | Base of BaseTypes.t

let pp = function
  | Base bt -> BaseTypes.pp bt

let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst _sym _sym' ls = ls

