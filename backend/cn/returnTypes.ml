open Subst
module SymSet = Set.Make(Sym)

module LRT = LogicalReturnTypes

type t = Computational of (Sym.t * BaseTypes.t) * LRT.t

let lrt (Computational (_, lrt)) = lrt


let to_logical = function
  | Computational ((name, bt), lrt) ->
     LRT.Logical ((name, Base bt), lrt)


let mComputational (name,bound) t = 
  Computational ((name,bound),t)


let concat (t1: t) (t2: LRT.t) : t = 
  match t1 with
  | Computational (bound, t1') -> 
     Computational (bound, LRT.concat t1' t2)




let subst_var (substitution: (Sym.t, Sym.t) Subst.t) = function
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t) 
     else if Sym.equal name substitution.after then
       let newname = Sym.fresh () in
       let t' = LRT.subst_var {before=name; after=newname} t in
       let t'' = LRT.subst_var substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt), LRT.subst_var substitution t)

let subst_vars = Subst.make_substs subst_var


let subst_it (substitution: (Sym.t, IndexTerms.t) Subst.t) rt = 
  let open Option in
  match rt with
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       return (Computational ((name,bt),t))
     else if SymSet.mem name (IndexTerms.vars_in substitution.after) then
       let newname = Sym.fresh () in
       let t' = LRT.subst_var {before=name; after=newname} t in
       let* t'' = LRT.subst_it substitution t' in
       return (Computational ((newname,bt), t''))
     else
       let* t = LRT.subst_it substitution t in
       return (Computational ((name,bt), t))




let freshify = function
  | Computational ((s,bt),t) ->
     let s' = Sym.fresh () in
     let t' = LRT.subst_var {before = s; after=s'} t in
     Computational ((s',bt), LRT.freshify t')
     




let free_vars = function
  | Computational ((sym,_),t) -> SymSet.remove sym (LRT.free_vars t)


let pp_aux rt = 
  let open Pp in
  match rt with
  | Computational ((name,bt),t) ->
     let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
     (op ^^^ typ (Sym.pp name) (BaseTypes.pp bt) ^^ dot) :: LRT.pp_aux t

let pp rt = 
  Pp.flow (Pp.break 1) (pp_aux rt)



let json = function
  | Computational ((s, bt), t) ->
     let args = [
         ("symbol", Sym.json s);
         ("basetype", BaseTypes.json bt);
         ("return_type", LRT.json t);
       ]
     in
     `Variant ("Computational", Some (`Assoc args))
