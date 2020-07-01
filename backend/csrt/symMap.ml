module CF=Cerb_frontend

include Map.Make (
  struct 
    type t = CF.Symbol.sym 
    let compare = CF.Symbol.symbol_compare
  end
)


