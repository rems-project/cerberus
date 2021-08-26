open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources.RE
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type 'i at = 
  | Computational of (Sym.t * BT.t) * 'i at
  | Logical of (Sym.t * LS.t) * 'i at
  | Resource of RE.t * 'i at
  | Constraint of LC.t * 'i at
  | I of 'i


type 'i t = 'i at

let mComputational (name, bound) t = Computational ((name,bound),t)
let mLogical (name, bound) t = Logical ((name,bound),t)
let mConstraint bound t = Constraint (bound,t)
let mResource bound t = Resource (bound,t)


let mComputationals t = List.fold_right mComputational t
let mLogicals t = List.fold_right mLogical t
let mConstraints t  = List.fold_right mConstraint t
let mResources t  = List.fold_right mResource t



let rec subst i_subst (substitution: (Sym.t, IT.t) Subst.t) at =
  match at with
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t)
     else if SymSet.mem name (IndexTerms.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst i_subst {before=name; after=IT.sym_ (newname, bt)} t in
       let t'' = subst i_subst substitution t' in
       Computational ((newname,bt),t'')
     else
       let t = subst i_subst substitution t in
       Computational ((name,bt),t)
  | Logical ((name,ls),t) -> 
     if Sym.equal name substitution.before then 
       Logical ((name,ls),t)
     else if SymSet.mem name (IndexTerms.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst i_subst {before=name; after=IT.sym_ (newname, ls)} t in
       let t'' = subst i_subst substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst i_subst substitution t in
       Logical ((name,ls),t')
  | Resource (re,t) -> 
     let re = RE.subst substitution re in
     let t = subst i_subst substitution t in
     Resource (re,t)
  | Constraint (lc,t) -> 
     let lc = LC.subst substitution lc in
     let t = subst i_subst substitution t in
     Constraint (lc,t)
  | I i -> 
     let i = i_subst substitution i in
     I i

let substs i_subst_it = Subst.make_substs (subst i_subst_it)


let pp i_pp ft = 
  let open Pp in
  let rec aux = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       group (op ^^^ typ (Sym.pp name) (BT.pp bt) ^^ dot) :: aux t
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2200}" else !^"AL" in
       group (op ^^^ typ (Sym.pp name) (LS.pp ls) ^^ dot) :: aux t
    | Resource (re,t) ->
       let op = minus ^^ star in
       group (RE.pp re ^^^ op) :: aux t
    | Constraint (lc,t) ->
       let op = equals ^^ rangle in
       group (LC.pp lc ^^^ op) :: aux t
    | I i -> 
       [i_pp i]
  in
  flow (break 1) (aux ft)


let rec get_return = function
  | Computational (_,ft) -> get_return ft
  | Logical (_,ft) -> get_return ft
  | Resource (_,ft) -> get_return ft
  | Constraint (_,ft) -> get_return ft
  | I rt -> rt


let rec count_computational = function
  | Computational (_,ft) -> 
     1 + count_computational ft
  | Logical (_,ft) 
    | Resource (_,ft)
    | Constraint (_,ft) -> 
     count_computational ft
  | I _ -> 0


module LRT = LogicalReturnTypes
module RT = ReturnTypes

let rec of_lrt (lrt : LRT.t) (rest : 'i t) : 'i t = 
  match lrt with
  | LRT.I -> rest
  | LRT.Logical ((name, t), args) -> Logical ((name, t), of_lrt args rest)
  | LRT.Resource (t, args) -> Resource (t, of_lrt args rest)
  | LRT.Constraint (t, args) -> Constraint (t, of_lrt args rest)


let rec logical_arguments_and_return (at : 'i t) : LRT.t * 'i =
  match at with
  | I r -> (LRT.I, r)
  | Logical ((name, t), args) -> 
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Logical ((name, t), lrt), r)
  | Resource (t, args) -> 
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Resource (t, lrt), r)
  | Constraint (t, args) -> 
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Constraint (t, lrt), r)
  | Computational (_, args) ->
     let (lrt, r) = logical_arguments_and_return args in
     (lrt, r)


let of_rt (rt : RT.t) (rest : 'i t) : 'i t = 
  let (RT.Computational ((name, t), lrt)) = rt in
  Computational ((name, t), of_lrt lrt rest)




type packing_ft = OutputDef.t t
type ft = ReturnTypes.t t
type lft = LogicalReturnTypes.t t
type lt = False.t t
