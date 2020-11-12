module CF=Cerb_frontend

type t = CF.Symbol.identifier

let s (CF.Symbol.Identifier (_,s)) = s

let pp id = PPrint.(!^)(s id)

let equal = CF.Symbol.idEqual

let compare id id' = String.compare (s id) (s id')

let parse loc id = CF.Symbol.Identifier (loc,id)


let subst _ id = id


