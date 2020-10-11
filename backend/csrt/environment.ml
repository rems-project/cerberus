module SymMap = Map.Make(Sym)
module LT = ArgumentTypes.Make(False)


type labels = LT.t SymMap.t

type expr_environment = 
  { global : Global.t; 
    labels : labels;
    local : Local.t;  }

type pexpr_environment = 
  { global : Global.t; 
    local : Local.t;  }




