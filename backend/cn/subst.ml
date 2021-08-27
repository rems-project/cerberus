open Pp

type 'a t = (Sym.t * 'a) list
type 'a subst = 'a t


let pp ppf subst = 
  Pp.list (fun (before, after) ->
      !^"replace" ^^^ Sym.pp before ^^^ !^"with" ^^^ ppf after
    ) subst



