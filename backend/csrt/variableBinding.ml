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


let pp ?(print_all_names = false) ?(print_used = false) (sym,binding) =
  match binding with
  | Computational (lname,bt) -> 
     !^"A" ^^^ parens (typ (Sym.pp sym) (parens (BT.pp false bt ^^ bar ^^ Sym.pp lname)))
  | Logical ls -> 
     !^"L" ^^^ parens (typ (Sym.pp sym) (LS.pp false ls))
  | Resource re -> 
     if print_all_names 
     then !^"R" ^^^ parens (typ (Sym.pp sym) (RE.pp false re))
     else !^"R" ^^^ parens (RE.pp false re )
  | UsedResource (re,_locs) -> 
     if not print_used then underscore 
     else if print_all_names then parens (!^"R" ^^^ (typ (Sym.pp sym) (!^"used" ^^^ RE.pp false re)))
     else parens (!^"R used" ^^^ RE.pp false re) 
  | Constraint lc -> 
     if print_all_names 
     then !^"C" ^^^ parens (typ (Sym.pp sym) (LC.pp false lc))
     else !^"C" ^^^ parens (LC.pp false lc )
