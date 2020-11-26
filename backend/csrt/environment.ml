module SymMap = Map.Make(Sym)
module LT = ArgumentTypes.Make(False)


type labels = LT.t SymMap.t

type t_impure = 
  { global : Global.t; 
    labels : labels;
    local : Local.t;  }

type t_pure = 
  { global : Global.t; 
    local : Local.t;  }




