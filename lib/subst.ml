open Pp

type 'a t =
  { replace : (Sym.t * 'a) list;
    relevant : Sym.Set.t;
    flags : Sym.Set.t
  }

type 'a subst = 'a t

let pp ppf subst =
  Pp.list
    (fun (before, after) -> !^"replace" ^^^ Sym.pp before ^^^ !^"with" ^^^ ppf after)
    subst


let make free_vars replace =
  let relevant =
    List.fold_right
      (fun (s, r) acc -> Sym.Set.union (free_vars r) (Sym.Set.add s acc))
      replace
      Sym.Set.empty
  in
  { replace; relevant; flags = Sym.Set.empty }


let add free_vars (s, r) subst =
  { subst with
    replace = (s, r) :: subst.replace;
    relevant = Sym.Set.union (free_vars r) (Sym.Set.add s subst.relevant)
  }
