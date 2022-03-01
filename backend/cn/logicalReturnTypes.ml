open Locations
module SymSet = Set.Make(Sym)
module Resources = Resources.RE
module IT = IndexTerms


type t = 
  | Logical of (Sym.t * LogicalSorts.t) * info * t
  | Define of (Sym.t * IT.t) * info * t
  | Resource of Resources.t * info * t
  | Constraint of LogicalConstraints.t * info * t
  | I

let rec concat (t1: t) (t2: t) : t = 
  match t1 with
  | I -> t2
  | Logical (bound, info, t) -> 
     Logical (bound, info, concat t t2)
  | Define (bound, info, t) ->
     Define (bound, info, concat t t2)
  | Resource (bound, info, t) -> 
     Resource (bound, info, concat t t2)
  | Constraint (bound, info, t) -> 
     Constraint (bound, info, concat t t2)

let (@@) = concat


let mLogical (name, bound, info) t = 
  Logical ((name, bound), info, t)
let mDefine (name, bound, info) t = 
  Define ((name, bound), info, t)
let mResource (bound, info) t = 
  Resource (bound, info, t)
let mConstraint (bound, info) t = 
  Constraint (bound, info, t)

let mLogicals = List.fold_right mLogical
let mDefines = List.fold_right mDefine
let mResources = List.fold_right mResource
let mConstraints = List.fold_right mConstraint


let rec subst (substitution: IT.t Subst.t) lrt = 
  match lrt with
  | Logical ((name, ls), info, t) -> 
     if SymSet.mem name substitution.relevant then
       let name' = Sym.fresh_same name in
       let t' = subst (IT.make_subst [(name, IT.sym_ (name', ls))]) t in
       let t'' = subst substitution t' in
       Logical ((name', ls), info, t'')
     else
       Logical ((name, ls), info, subst substitution t)
    | Define ((name, it), info, t) ->
       let it = IT.subst substitution it in
       if SymSet.mem name substitution.relevant then
         let name' = Sym.fresh_same name in
         let t' = subst (IT.make_subst [(name, IT.sym_ (name', IT.bt it))]) t in
         let t'' = subst substitution t' in
         Define ((name', it), info, t'')
       else
         Define ((name, it), info, subst substitution t)
  | Resource (re, info, t) -> 
     let re = Resources.subst substitution re in
     let t = subst substitution t in
     Resource (re, info, t)
  | Constraint (lc, info, t) -> 
     let lc = LogicalConstraints.subst substitution lc in
     let t = subst substitution t in
     Constraint (lc, info, t)
  | I -> 
     I






let rec pp_aux lrt =
  let open Pp in
  match lrt with
  | Logical ((name, ls), _info, t) ->
     let op = if !unicode then utf8string "\u{2203}" else !^"E" in
     group (op ^^^ typ (Sym.pp name) (LogicalSorts.pp ls) ^^ dot) :: pp_aux t
  | Define ((name, it), _info, t) ->
     group (!^"let" ^^^ (Sym.pp name) ^^^ equals ^^^ IT.pp it ^^ dot) :: pp_aux t
  | Resource (re, _info, t) ->
     let op = star in
     group (Resources.pp re ^^^ op) :: pp_aux t
  | Constraint (lc, _info, t) ->
     let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
     group (LogicalConstraints.pp lc ^^^ op) :: pp_aux t
  | I -> 
     [!^"I"]

let pp rt = 
  Pp.flow (Pp.break 1) (pp_aux rt) 



let rec json = function
  | Logical ((s, ls), _info, t) ->
     let args = [
         ("symbol", Sym.json s);
         ("sort", LogicalSorts.json ls);
         ("return_type", json t);
       ]
     in
     `Variant ("Logical", Some (`Assoc args))
  | Define ((s, it), _info, t) ->
     let args = [
         ("symbol", Sym.json s);
         ("term", IT.json it);
         ("return_type", json t);
       ]
     in
     `Variant ("Define", Some (`Assoc args))
  | Resource (r, _info, t) ->
     let args = [
         ("resource", Resources.json r);
         ("return_type", json t);
       ]
     in
     `Variant ("Resource", Some (`Assoc args))
  | Constraint (lc, _info, t) ->
     let args = [
         ("constraint", LogicalConstraints.json lc);
         ("return_type", json t);
       ]
     in
     `Variant ("Constraint", Some (`Assoc args))
  | I ->
     `Variant ("I", None)
     
