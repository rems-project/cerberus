module Loc = Locations
module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints

open Pp

open Kind

type bound =
  | Computational of Sym.t * BT.t
  | Logical of LS.t
  | Resource of RE.t
  | Constraint of LC.t

type binding = Sym.t * bound


let kind = function
  | Computational _ -> KComputational
  | Logical _ -> KLogical
  | Resource _ -> KResource
  | Constraint _ -> KConstraint


let is_computational = function
  | Computational (sym,bt) -> Some (sym, bt)
  | _ -> None

let is_logical = function
  | Logical ls -> Some ls
  | _ -> None

let is_resource = function
  | Resource re -> Some re
  | _ -> None

let is_constraint = function
  | Constraint lc -> Some lc
  | _ -> None



let pp ?(print_all_names = false) (sym,binding) =
  let btyp sym pped = format [Bold] (Sym.pp_string sym) ^^ colon ^^ pped in
  match binding with
  | Computational (lname,bt) -> 
     btyp sym (BT.pp bt ^^ tilde ^^ Sym.pp lname)
  | Logical ls -> 
     btyp sym (LS.pp ls)
  | Resource re -> 
     if print_all_names 
     then btyp sym (squotes (RE.pp re))
     else squotes (RE.pp re)
  | Constraint lc -> 
     if print_all_names 
     then btyp sym (LC.pp lc)
     else LC.pp lc







