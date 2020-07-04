open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type t = 
  | I
  | Computational of Sym.t * BT.t * t
  | Logical of Sym.t * LS.t * t
  | Resource of RE.t * t
  | Constraint of LC.t * t



let mcomputational name bound t = 
  Computational (name,bound,t)
let mlogical name bound t = 
  Logical (name,bound,t)
let mconstraint bound t = 
  Constraint (bound,t)
let mresource bound t = 
  Resource (bound,t)



let rec (@@) (t1: t) (t2: t) :t = 
  match t1 with
  | I -> t2
  | Computational (name,bound,t) -> 
     Computational (name,bound, t@@t2)
  | Logical (name,bound,t) -> 
     Logical (name,bound, t@@t2)
  | Resource (bound,t) -> 
     Resource (bound, t@@t2)
  | Constraint (bound,t) -> 
     Constraint (bound, t@@t2)



let rec subst_var substitution = function
  | I -> I
  | Computational (name,bt,t) -> 
     if name = substitution.substitute then 
       Computational (name,bt,t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var {substitute=name; swith=IT.S newname} t in
       let t'' = subst_var substitution t' in
       Computational (newname,bt,t'')
     else
       Computational (name,bt,subst_var substitution t)
  | Logical (name,ls,t) -> 
     if name = substitution.substitute then 
       Logical (name,ls,t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var {substitute=name; swith=IT.S newname} t in
       let t'' = subst_var substitution t' in
       Logical (newname,ls,t'')
     else
       let t' = subst_var substitution t in
       Logical (name,ls,t')
  | Resource (re,t) -> 
     let re = RE.subst_var substitution re in
     let t = subst_var substitution t in
     Resource (re,t)
  | Constraint (lc,t) -> 
     let lc = LC.subst_var substitution lc in
     let t = subst_var substitution t in
     Constraint (lc,t)

let subst_vars = Subst.make_substs subst_var


let rec instantiate_struct_member subst rt =
  match rt with
  | I -> I
  | Computational (name,bound,t) -> 
     Computational (name,bound,instantiate_struct_member subst t)
  | Logical (name,bound,t) -> 
     Logical (name,bound,instantiate_struct_member subst t)
  | Resource (bound,t) -> 
     Resource (RE.instantiate_struct_member subst bound, 
               instantiate_struct_member subst t)
  | Constraint (bound,t) -> 
     Constraint (LC.instantiate_struct_member subst bound, 
                 instantiate_struct_member subst t)


let pp rt = 
  let open Pp in
  let rec aux = function
    | Computational (name,bt,t) ->
       let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
       (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux t
    | Logical (name,ls,t) ->
       let op = if !unicode then utf8string "\u{2203}" else !^"E" in
       (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux t
    | Resource (re,t) ->
       let op = if !unicode then utf8string "\u{2217}" else star in
       (RE.pp false re ^^^ op) :: aux t
    | Constraint (lc,t) ->
       let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
       (LC.pp false lc ^^^ op) :: aux t
    | I -> 
       [!^"I"]
  in
  flow (break 1) (aux rt)





