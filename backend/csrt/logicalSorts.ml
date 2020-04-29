open List
open Except
module Loc=Location

type t = 
  | Base of BaseTypes.t

let pp = function
  | Base bt -> BaseTypes.pp bt

let parse_sexp loc (names : NameMap.t) sx =
  match sx with
  | sx ->
     BaseTypes.parse_sexp loc names sx >>= fun (bt,names) ->
     return (Base bt, names)

let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst _sym _sym' ls = ls

