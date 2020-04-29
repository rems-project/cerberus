open Cerb_frontend

type t = Symbol.identifier

let s (Symbol.Identifier (_,s)) = s

let pp = s

let compare id id' = 
  String.compare (s id) (s id')

let parse loc id = 
  Symbol.Identifier (loc,id)


