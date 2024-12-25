module CF = Cerb_frontend

type t = CF.Symbol.identifier

let get_string (CF.Symbol.Identifier (_, s)) = s

let get_loc (CF.Symbol.Identifier (loc, _)) = loc

let pp id = PPrint.( !^ ) (get_string id)

let equal = CF.Symbol.idEqual

let compare id id' = String.compare (get_string id) (get_string id')

let make loc id = CF.Symbol.Identifier (loc, id)

let equal_string str id = String.equal (get_string id) str

let subst _ id = id
