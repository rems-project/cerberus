module Loc=Locations
module SymSet = Set.Make(Sym)


type t = Base of BaseTypes.t
type sort = t                      

let pp (Base bt) = BaseTypes.pp bt

let json (Base bt) : Yojson.Safe.t = 
  BaseTypes.json bt

let equal (Base t1) (Base t2) = BaseTypes.equal t1 t2

