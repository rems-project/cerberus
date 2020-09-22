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
  let btyp sym pped = 
    format [Pp.FG(Default,Bright)] (Sym.pp_string sym) ^^ colon ^^ pped in
  match binding with
  | Computational (lname,bt) -> 
     btyp sym (BT.pp true bt ^^ tilde ^^ Sym.pp lname)
  | Logical ls -> 
     btyp sym (LS.pp false ls)
  | Resource re -> 
     if print_all_names 
     then btyp sym (squotes (RE.pp false re))
     else squotes (RE.pp false re)
  | UsedResource (re,_locs) -> 
     if not print_used then underscore 
     else if print_all_names 
     then btyp sym (!^"used" ^^^ (squotes (RE.pp false re)))
     else !^"used" ^^^ squotes (RE.pp false re)
  | Constraint lc -> 
     if print_all_names 
     then btyp sym (dquotes (LC.pp false lc))
     else dquotes (LC.pp false lc)
