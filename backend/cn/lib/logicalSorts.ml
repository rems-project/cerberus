module Loc = Locations

type t = BaseTypes.t

type sort = t

let pp bt = BaseTypes.pp bt

let json bt : Yojson.Safe.t = BaseTypes.json bt

let equal t1 t2 = BaseTypes.equal t1 t2
