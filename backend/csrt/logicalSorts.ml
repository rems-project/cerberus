module Loc=Locations
module SymSet = Set.Make(Sym)


type t = Base of BaseTypes.t
type sort = t                      

let pp atomic (Base bt) = BaseTypes.pp atomic bt

let equal (Base t1) (Base t2) = BaseTypes.equal t1 t2

