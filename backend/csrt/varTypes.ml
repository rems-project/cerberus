open PPrint
open Pp_tools


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

let subst sym with_it t = 
 match t with
 | A t -> A (BaseTypes.subst sym with_it t)
 | L t -> L (LogicalSorts.subst sym with_it t)
 | R t -> R (Resources.subst sym with_it t)
 | C t -> C (LogicalConstraints.subst sym with_it t)



let pp = function
  | A t -> char 'A' ^^^ (BT.pp t)
  | L t -> char 'L' ^^^ (LS.pp t)
  | R t -> char 'R' ^^^ (RE.pp t)
  | C t -> char 'C' ^^^ (LC.pp t)




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

