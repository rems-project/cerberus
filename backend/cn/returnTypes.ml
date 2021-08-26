open Subst
module SymSet = Set.Make(Sym)
module IT = IndexTerms

module LRT = LogicalReturnTypes

type t = Computational of (Sym.t * BaseTypes.t) * LRT.t

let lrt (Computational (_, lrt)) = lrt


let to_logical = function
  | Computational ((name, bt), lrt) ->
     LRT.Logical ((name, bt), lrt)


let mComputational (name,bound) t = 
  Computational ((name,bound),t)


let concat (t1: t) (t2: LRT.t) : t = 
  match t1 with
  | Computational (bound, t1') -> 
     Computational (bound, LRT.concat t1' t2)



let subst (substitution: (Sym.t, IT.t) Subst.t) rt = 
  match rt with
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t)
     else if SymSet.mem name (IndexTerms.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = LRT.subst {before=name; after=IT.sym_ (newname, bt)} t in
       let t'' = LRT.subst substitution t' in
       Computational ((newname,bt), t'')
     else
       let t = LRT.subst substitution t in
       Computational ((name,bt), t)




let freshify = function
  | Computational ((s,bt),t) ->
     let s' = Sym.fresh () in
     let t' = LRT.subst {before = s; after=IT.sym_ (s', bt)} t in
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
