open Pp


module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts

type t = 
 | A of BaseTypes.t
 | L of LogicalSorts.t
 | R of Resources.t
 | C of LogicalConstraints.t

let subst_var subst t = 
 match t with
 | A t -> A (BaseTypes.subst_var subst t)
 | L t -> L (LogicalSorts.subst_var subst t)
 | R t -> R (Resources.subst_var subst t)
 | C t -> C (LogicalConstraints.subst_var subst t)

let subst_vars = Tools.make_substs subst_var


let pp = function
  | A t -> char 'A' ^^^ (BT.pp false t)
  | L t -> char 'L' ^^^ (LS.pp false t)
  | R t -> char 'R' ^^^ (RE.pp false t)
  | C t -> char 'C' ^^^ (LC.pp false t)




type kind = 
  | Argument
  | Logical
  | Resource
  | Constraint

let kind = function
  | A _ -> Argument
  | L _ -> Logical
  | R _ -> Resource
  | C _ -> Constraint

let pp_kind = function
  | Argument -> !^"computational"
  | Logical -> !^"logical"
  | Resource -> !^"resource"
  | Constraint -> !^"constraint"



