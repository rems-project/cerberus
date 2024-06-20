module SymPair = struct
  type t = Sym.t * Sym.t
  let compare a b = Lem_basic_classes.pairCompare Sym.compare Sym.compare a b
end


include Pset
(*
type t = SymPair.t Pset.set
let empty = Pset.empty SymPair.compare
let transitiveClosure = Pset.tc SymPair.compare
*)
