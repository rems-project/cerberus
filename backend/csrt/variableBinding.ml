module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module BT = BaseTypes
module LS = LogicalSorts

open Pp


type t =
  | Computational of Sym.t * BT.t
  | Logical of LS.t
  | Resource of RE.t
  | UsedResource of RE.t * Loc.t list
  | Constraint of LC.t


let pp print_used (sym,binding) =
  match binding with
  | Computational (lname,bt) -> 
     !^"A" ^^^ parens (typ (Sym.pp sym) (parens (BT.pp false bt ^^ bar ^^ Sym.pp lname)))
  | Logical ls -> 
     !^"L" ^^^ parens (typ (Sym.pp sym) (LS.pp false ls))
  | Resource re -> 
     !^"R" ^^^ parens (RE.pp false re )
  | UsedResource (re,_locs) -> 
     if print_used then parens (!^"R used" ^^^ RE.pp false re) 
     else underscore
  | Constraint lc -> 
     !^"C" ^^^ parens (LC.pp false lc )
