open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type 'i at = 
  | Computational of (Sym.t * BT.t) * info * 'i at
  | Define of (Sym.t * IT.t) * info * 'i at
  | Resource of (Sym.t * (RET.t * BT.t)) * info * 'i at
  | Constraint of LC.t * info * 'i at
  | I of 'i


type 'i t = 'i at

let mComputational (name, bound, info) t = 
  Computational ((name, bound), info, t)
let mDefine (name, it, info) t = 
  Define ((name, it), info, t)
let mResource (bound, info) t = 
  Resource (bound, info, t)
let mConstraint (bound, info) t = 
  Constraint (bound, info, t)


let mComputationals t = List.fold_right mComputational t
let mDefines t = List.fold_right mDefine t
let mResources t  = List.fold_right mResource t
let mConstraints t  = List.fold_right mConstraint t



let rec subst i_subst =
  let rec aux (substitution: IT.t Subst.t) at =
    match at with
    | Computational ((name, bt), info, t) -> 
       let name, t = suitably_alpha_rename i_subst substitution.relevant (name, bt) t in
       Computational ((name, bt), info, aux substitution t)
    | Define ((name, it), info, t) ->
       let it = IT.subst substitution it in
       let name, t = suitably_alpha_rename i_subst substitution.relevant (name, IT.bt it) t in
       Define ((name, it), info, aux substitution t)
    | Resource ((name, (re, bt)), info, t) -> 
       let re = RET.subst substitution re in
       let name, t = suitably_alpha_rename i_subst substitution.relevant (name, bt) t in
       let t = aux substitution t in
       Resource ((name, (re, bt)), info, t)
    | Constraint (lc, info, t) -> 
       let lc = LC.subst substitution lc in
       let t = aux substitution t in
       Constraint (lc, info, t)
    | I i -> 
       let i = i_subst substitution i in
       I i
  in
  aux

and alpha_rename i_subst (s, ls) t = 
  let s' = Sym.fresh_same s in
  (s', subst i_subst (IT.make_subst [(s, IT.sym_ (s', ls))]) t)

and suitably_alpha_rename i_subst syms (s, ls) t = 
  if SymSet.mem s syms 
  then alpha_rename i_subst (s, ls) t
  else (s, t)



let pp i_pp ft = 
  let open Pp in
  let rec aux = function
    | Computational ((name, bt), _info, t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       group (op ^^^ typ (Sym.pp name) (BT.pp bt) ^^ dot) :: aux t
    | Define ((name, it), _info, t) ->
       group (!^"let" ^^^ (Sym.pp name) ^^^ equals ^^^ IT.pp it ^^ semi) :: aux t       
    | Resource ((name, (re, _bt)), _info, t) ->
       group (!^"let" ^^^ (Sym.pp name) ^^^ equals ^^^ RET.pp re ^^ semi) :: aux t
    | Constraint (lc, _info, t) ->
       let op = equals ^^ rangle in
       group (LC.pp lc ^^^ op) :: aux t
    | I i -> 
       [i_pp i]
  in
  flow (break 1) (aux ft)


let rec get_return = function
  | Computational (_, _, ft) -> get_return ft
  | Define (_, _, ft) -> get_return ft
  | Resource (_, _, ft) -> get_return ft
  | Constraint (_, _, ft) -> get_return ft
  | I rt -> rt


let rec count_computational = function
  | Computational (_, _, ft) -> 
     1 + count_computational ft
  | Define (_, _, ft) ->
     count_computational ft
  | Resource (_, _, ft) ->
     count_computational ft
  | Constraint (_, _, ft) -> 
     count_computational ft
  | I _ -> 0


module LRT = LogicalReturnTypes
module RT = ReturnTypes


let alpha_unique =
  let rename_if ss = suitably_alpha_rename RT.subst ss in
  let rec f ss at =
    match at with
    | Computational ((name, bt), info, t) ->
       let name, t = rename_if ss (name, bt) t in
       let t = f (SymSet.add name ss) t in
       Computational ((name, bt), info, t)
    | Define ((name, it), info, t) ->
       let name, t = rename_if ss (name, IT.bt it) t in
       let t = f (SymSet.add name ss) t in
       Define ((name, it), info, t)
    | Resource ((name, (re, bt)), info, t) ->
       let name, t = rename_if ss (name, bt) t in
       let t = f (SymSet.add name ss) t in
       Resource ((name, (re, bt)), info, f ss t)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I i -> I (RT.alpha_unique ss i)
  in
  f SymSet.empty


let rec of_lrt (lrt : LRT.t) (rest : 'i t) : 'i t = 
  match lrt with
  | LRT.I -> 
     rest
  | LRT.Define ((name, it), info, args) ->
     Define ((name, it), info, of_lrt args rest)
  | LRT.Resource ((name, t), info, args) -> 
     Resource ((name, t), info, of_lrt args rest)
  | LRT.Constraint (t, info, args) -> 
     Constraint (t, info, of_lrt args rest)


let rec logical_arguments_and_return (at : 'i t) : LRT.t * 'i =
  match at with
  | I r -> 
     (LRT.I, r)
  | Define ((name, it), info, args) ->
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Define ((name, it), info, lrt), r)
  | Resource ((name, t), info, args) -> 
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Resource ((name, t), info, lrt), r)
  | Constraint (t, info, args) -> 
     let (lrt, r) = logical_arguments_and_return args in
     (LRT.Constraint (t, info, lrt), r)
  | Computational (_, info, args) ->
     let (lrt, r) = logical_arguments_and_return args in
     (lrt, r)


let of_rt (rt : RT.t) (rest : 'i t) : 'i t = 
  let (RT.Computational ((name, t), info, lrt)) = rt in
  Computational ((name, t), info, of_lrt lrt rest)



let rec map (f : 'i -> 'j) (at : 'i at) : 'j at =
  match at with
  | Computational (bound, info, at) -> 
     Computational (bound, info, map f at)
  | Define (bound, info, at) ->
     Define (bound, info, map f at)
  | Resource (bound, info, at) -> 
     Resource (bound, info, map f at)
  | Constraint (lc, info, at) -> 
     Constraint (lc, info, map f at)
  | I i ->
     I (f i)




type packing_ft = OutputDef.t t
type ft = ReturnTypes.t t
type lft = LogicalReturnTypes.t t
type lt = False.t t

  
