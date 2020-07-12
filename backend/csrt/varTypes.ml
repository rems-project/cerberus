open Pp


module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts

type used = 
  | Used of Loc.t
  | Unused

type t = 
 | A of BaseTypes.t
 | L of LogicalSorts.t
 | R of Resources.t * used
 | C of LogicalConstraints.t


let pp with_prefix = 
  let prefix c = if with_prefix then char c else empty in
  function
  | A t -> prefix 'A' ^^^ (BT.pp false t)
  | L t -> prefix 'L' ^^^ (LS.pp false t)
  | R (t,Unused) -> prefix 'R' ^^^ (RE.pp false t)
  | R (t,Used l) -> parens (!^"used" ^^^ prefix 'R' ^^^ (RE.pp false t))
  | C t -> prefix 'C' ^^^ (LC.pp false t)


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




