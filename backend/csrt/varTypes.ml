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

let subst_var sym with_it t = 
 match t with
 | A t -> A (BaseTypes.subst_var sym with_it t)
 | L t -> L (LogicalSorts.subst_var sym with_it t)
 | R t -> R (Resources.subst_var sym with_it t)
 | C t -> C (LogicalConstraints.subst_var sym with_it t)

let concretise_field id with_it t = 
 match t with
 | C t -> C (LogicalConstraints.concretise_field id with_it t)
 | _ -> t



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

