open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type l = 
  | Logical of (Sym.t * LS.t) * l
  | Resource of RE.t * l
  | Constraint of LC.t * l
  | I

type t = Computational of (Sym.t * BT.t) * l


let mComputational (name,bound) t = Computational ((name,bound),t)
let mLogical (name,bound) t = Logical ((name,bound),t)
let mConstraint bound t = Constraint (bound,t)
let mResource bound t = Resource (bound,t)



let rec (@@) (t1: l) (t2: l) : l = 
  match t1 with
  | I -> t2
  | Logical ((name,bound),t) -> Logical ((name,bound), t@@t2)
  | Resource (bound,t) -> Resource (bound, t@@t2)
  | Constraint (bound,t) -> Constraint (bound, t@@t2)


let subst_var_l ?(re_subst_var=RE.subst_var) substitution lrt = 
  let rec aux substitution = function
    | I -> I
    | Logical ((name,ls),t) -> 
       if Sym.equal name substitution.before then 
         Logical ((name,ls),t) 
       else if SymSet.mem name (IT.vars_in substitution.after) then
         let newname = Sym.fresh () in
         let t' = aux {before=name;after=S newname} t in
         let t'' = aux substitution t' in
         Logical ((newname,ls),t'')
       else
         let t' = aux substitution t in
         Logical ((name,ls),t')
    | Resource (re,t) -> 
       let re = re_subst_var substitution re in
       let t = aux substitution t in
       Resource (re,t)
    | Constraint (lc,t) -> 
       let lc = LC.subst_var substitution lc in
       let t = aux substitution t in
       Constraint (lc,t)
  in
  aux substitution lrt


let subst_var substitution = function
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t) 
     else if SymSet.mem name (IT.vars_in substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst_var_l {before=name; after=S newname} t in
       let t'' = subst_var_l substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_var_l substitution t)

let subst_vars = Subst.make_substs subst_var



let rec freshify_l = function
  | Logical ((s,ls),t) ->
     let s' = Sym.fresh () in
     let t' = subst_var_l {before=s;after=S s'} t in
     Logical ((s',ls), freshify_l t')
  | Resource (re,t) ->
     Resource (re, freshify_l t)
  | Constraint (lc,t) ->
     Constraint (lc, freshify_l t)
  | I -> 
     I


let freshify = function
  | Computational ((s,bt),t) ->
     let s' = Sym.fresh () in
     let t' = subst_var_l {before = s; after=S s'} t in
     Computational ((s',bt), freshify_l t')
     


let rec instantiate_struct_member_l subst rt =
  match rt with
  | I -> I
  | Logical ((name,bound),t) -> 
     Logical ((name,bound),instantiate_struct_member_l subst t)
  | Resource (bound,t) -> 
     Resource (bound, instantiate_struct_member_l subst t)
  | Constraint (bound,t) -> 
     Constraint (LC.instantiate_struct_member subst bound, 
                 instantiate_struct_member_l subst t)

let instantiate_struct_member subst = function
  | Computational ((name,bound),t) -> 
     Computational ((name,bound),instantiate_struct_member_l subst t)

let rec free_vars_l = function
  | Logical ((sym,_),t) -> SymSet.remove sym (free_vars_l t)
  | Resource (r,t) -> SymSet.union (RE.vars_in r) (free_vars_l t)
  | Constraint (c,t) -> SymSet.union (LC.vars_in c) (free_vars_l t)
  | I -> SymSet.empty

let free_vars = function
  | Computational ((sym,_),t) -> SymSet.remove sym (free_vars_l t)


let (pp,pp_l) = 
  
  let open Pp in

  let rec aux_l = function
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2203}" else !^"E" in
       (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux_l t
    | Resource (re,t) ->
       let op = if !unicode then utf8string "\u{2217}" else star in
       (RE.pp re ^^^ op) :: aux_l t
    | Constraint (lc,t) ->
       let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
       (LC.pp lc ^^^ op) :: aux_l t
    | I -> 
       [!^"I"]
  in

  let aux = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
       (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux_l t
  in

  let pp_l rt = flow (break 1) (aux_l rt) in
  let pp rt = flow (break 1) (aux rt) in

  (pp,pp_l)


