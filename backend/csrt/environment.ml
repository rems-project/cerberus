module SymMap = Map.Make(Sym)
module LT = ArgumentTypes.Make(False)



type label_kind = 
  | Return
  | Loop
  | Other


type labels = (LT.t * label_kind) SymMap.t

type t_impure = 
  { global : Global.t; 
    labels : labels;
    local : Local.t;  }

type t_pure = 
  { global : Global.t; 
    local : Local.t;  }




