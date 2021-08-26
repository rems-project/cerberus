open Subst
module SymSet = Set.Make(Sym)
module Resources = Resources.RE
module IT = IndexTerms


type t = 
  | Logical of (Sym.t * LogicalSorts.t) * t
  | Resource of Resources.t * t
  | Constraint of LogicalConstraints.t * t
  | I

let rec concat (t1: t) (t2: t) : t = 
  match t1 with
  | I -> t2
  | Logical (bound,t) -> Logical (bound, concat t t2)
  | Resource (bound,t) -> Resource (bound, concat t t2)
  | Constraint (bound,t) -> Constraint (bound, concat t t2)

let (@@) = concat


let mLogical (name,bound) t = Logical ((name,bound),t)
let mConstraint bound t = Constraint (bound,t)
let mResource bound t = Resource (bound,t)

let mLogicals = List.fold_right mLogical
let mConstraints = List.fold_right mConstraint
let mResources = List.fold_right mResource


let rec subst (substitution: (Sym.t, IndexTerms.t) Subst.t) lrt = 
  match lrt with
  | I -> 
     I
  | Logical ((name,ls),t) -> 
     if Sym.equal name substitution.before then 
       Logical ((name,ls),t)
     else if SymSet.mem name (IndexTerms.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst {before=name;after=IT.sym_ (newname, ls)} t in
       let t'' = subst substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst substitution t in
       Logical ((name,ls),t')
  | Resource (re,t) -> 
     let re = Resources.subst substitution re in
     let t = subst substitution t in
     Resource (re,t)
  | Constraint (lc,t) -> 
     let lc = LogicalConstraints.subst substitution lc in
     let t = subst substitution t in
     Constraint (lc,t)

let substs = Subst.make_substs subst



let rec freshify = function
  | Logical ((s,ls),t) ->
     let s' = Sym.fresh () in
     let t' = subst {before=s;after=IT.sym_ (s', ls)} t in
     Logical ((s',ls), freshify t')
  | Resource (re,t) ->
     Resource (re, freshify t)
  | Constraint (lc,t) ->
     Constraint (lc, freshify t)
  | I -> 
     I


let rec free_vars = function
  | Logical ((sym,_),t) -> SymSet.remove sym (free_vars t)
  | Resource (r,t) -> SymSet.union (Resources.free_vars r) (free_vars t)
  | Constraint (c,t) -> SymSet.union (LogicalConstraints.free_vars c) (free_vars t)
  | I -> SymSet.empty



let rec pp_aux lrt =
  let open Pp in
  match lrt with
  | Logical ((name,ls),t) ->
     let op = if !unicode then utf8string "\u{2203}" else !^"E" in
     group (op ^^^ typ (Sym.pp name) (LogicalSorts.pp ls) ^^ dot) :: pp_aux t
  | Resource (re,t) ->
     let op = star in
     group (Resources.pp re ^^^ op) :: pp_aux t
  | Constraint (lc,t) ->
     let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
     group (LogicalConstraints.pp lc ^^^ op) :: pp_aux t
  | I -> 
     [!^"I"]

let pp rt = 
  Pp.flow (Pp.break 1) (pp_aux rt) 



let rec json = function
  | Logical ((s, ls), t) ->
     let args = [
         ("symbol", Sym.json s);
         ("sort", LogicalSorts.json ls);
         ("return_type", json t);
       ]
     in
     `Variant ("Logical", Some (`Assoc args))
  | Resource (r,t) ->     
     let args = [
         ("resource", Resources.json r);
         ("return_type", json t);
       ]
     in
     `Variant ("Resource", Some (`Assoc args))
  | Constraint (lc,t) ->
     let args = [
         ("constraint", LogicalConstraints.json lc);
         ("return_type", json t);
       ]
     in
     `Variant ("Constraint", Some (`Assoc args))
  | I ->
     `Variant ("I", None)
     
