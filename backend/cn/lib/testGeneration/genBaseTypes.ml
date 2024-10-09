module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints

type t = Sym.t option * BT.t [@@deriving eq, ord]

let pred ((psym, _) : t) : Sym.t option = psym

let bt ((_, bt) : t) : BT.t = bt

let pp ((psym, bt) : t) : Pp.document =
  let open Pp in
  BT.pp bt ^^ space ^^ at ^^ Option.pp Sym.pp psym


let of_bt ?(pred_sym : Sym.t option = None) (bt : BT.t) : t = (pred_sym, bt)
