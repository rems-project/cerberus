module Loc=Locations
module SymSet = Set.Make(Sym)
module BT = BaseTypes
(* open PPrint *)
(* open Pp_tools *)


type t = Base of BaseTypes.t
                      

let pp atomic = function
  | Base bt -> BaseTypes.pp atomic bt

let equal (Base t1) (Base t2) = 
  BT.equal t1 t2

