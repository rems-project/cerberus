module SymSet = Set.Make(Sym)

open Pp

type 'a t = {
    replace : (Sym.t * 'a) list;
    relevant : SymSet.t
  }
type 'a subst = 'a t


let pp ppf subst = 
  Pp.list (fun (before, after) ->
      !^"replace" ^^^ Sym.pp before ^^^ !^"with" ^^^ ppf after
    ) subst



let make free_vars replace = 
  let relevant = 
    List.fold_right (fun (s, r) acc ->
        SymSet.union (free_vars r) (SymSet.add s acc)
      ) replace SymSet.empty
  in
  { replace; relevant }
