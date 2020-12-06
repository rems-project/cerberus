open Pp

type t = 
  | KComputational
  | KLogical
  | KResource
  | KConstraint
  | KUsedResource

type kind = t

let pp = function
  | KComputational -> !^"computatinoal variable"
  | KLogical -> !^"logical variable"
  | KResource -> !^"resource"
  | KConstraint -> !^"constraint"
  | KUsedResource -> !^"used resource"
