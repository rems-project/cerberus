module Loc=Locations
module SymSet = Set.Make(Sym)
module BT = BaseTypes


type t = Base of BaseTypes.t
                      

let pp atomic (Base bt) = 
  BaseTypes.pp atomic bt

let equal (Base t1) (Base t2) = 
  BT.equal t1 t2

