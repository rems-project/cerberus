open Pp

type t = 
  | KComputational
  | KLogical

type kind = t

let pp = function
  | KComputational -> !^"computatinoal variable"
  | KLogical -> !^"logical variable"
