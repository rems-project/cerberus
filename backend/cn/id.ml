module CF=Cerb_frontend

type t = CF.Symbol.identifier

let s (CF.Symbol.Identifier (_,s)) = s

let loc (CF.Symbol.Identifier (loc,_)) = loc

let pp_string id = s id
let pp id = PPrint.(!^)(s id)

let equal = CF.Symbol.idEqual

let compare id id' = String.compare (s id) (s id')

let parse loc id = CF.Symbol.Identifier (loc,id)

let id id =
  let here = Locations.other __FUNCTION__ in
  CF.Symbol.Identifier (here,id)

let is_str str id = String.equal (s id) str


let subst _ id = id


