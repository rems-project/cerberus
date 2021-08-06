open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources.RE
module LC = LogicalConstraints
module AT = ArgumentTypes
module SymSet = Set.Make(Sym)



type 'rt c = I of 'rt
           | Constraint of LC.t * 'rt c
type 'rt r = C of 'rt c 
           | Resource of RE.t * 'rt r 
type 'rt l = R of 'rt r
           | Logical of (Sym.t * LS.t) * 'rt l
type 'rt a = L of 'rt l 
           | Computational of (Sym.t * BT.t) * 'rt a

type 'rt t = 'rt a


let mcomputational (name,bound) t = Computational ((name,bound),t)
let mlogical (name,bound) t = Logical ((name,bound),t)
let mconstraint bound t = Constraint (bound,t)
let mresource bound t = Resource (bound,t)


let rec subst_var_c i_subst_var substitution = function
  | Constraint (lc, t) -> 
     Constraint (LC.subst_var substitution lc, 
                 subst_var_c i_subst_var substitution t)
  | I rt -> 
     I (i_subst_var substitution rt)

let rec subst_var_r i_subst_var substitution = function
  | Resource (re, t) ->
     Resource (RE.subst_var substitution re, 
               subst_var_r i_subst_var substitution t)
  | C c -> 
     C (subst_var_c i_subst_var substitution c)

let rec subst_var_l i_subst_var substitution = function
  | Logical ((name,ls),t) -> 
     if Sym.equal name substitution.before then 
       Logical ((name,ls),t) 
     else if Sym.equal name substitution.after then
       let newname = Sym.fresh () in
       let t' = subst_var_l i_subst_var {before=name; after=newname} t in
       let t'' = subst_var_l i_subst_var substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst_var_l i_subst_var substitution t in
       Logical ((name,ls),t')
  | R r -> 
     R (subst_var_r i_subst_var substitution r)

let rec subst_var_a i_subst_var substitution = function
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t) 
     else if Sym.equal name substitution.after then
       let newname = Sym.fresh () in
       let t' = subst_var_a i_subst_var {before=name; after=newname} t in
       let t'' = subst_var_a i_subst_var substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_var_a i_subst_var substitution t)
  | L l -> L (subst_var_l i_subst_var substitution l)

let subst_vars_l i_subst_var = Subst.make_substs (subst_var_l i_subst_var)
let subst_vars_r i_subst_var = Subst.make_substs (subst_var_r i_subst_var)
let subst_vars_c i_subst_var = Subst.make_substs (subst_var_c i_subst_var)
let subst_vars_a i_subst_var = Subst.make_substs (subst_var_a i_subst_var)

let subst_var = subst_var_a
let subst_vars = subst_vars_a






let rec subst_it_c i_subst_it substitution = function
  | Constraint (lc, t) -> 
     Constraint (LC.subst_it substitution lc, 
                 subst_it_c i_subst_it substitution t)
  | I rt -> 
     I (i_subst_it substitution rt)

let rec subst_it_r i_subst_it substitution = function
  | Resource (re, t) ->
     Resource (RE.subst_it substitution re, 
               subst_it_r i_subst_it substitution t)
  | C c -> 
     C (subst_it_c i_subst_it substitution c)

let rec subst_it_l i_subst_it substitution = function
  | Logical ((name,ls),t) -> 
     if Sym.equal name substitution.before then 
       Logical ((name,ls),t) 
     else if SymSet.mem name (IT.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst_it_l i_subst_it {before=name; after=IT.sym_ (newname, ls)} t in
       let t'' = subst_it_l i_subst_it substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst_it_l i_subst_it substitution t in
       Logical ((name,ls),t')
  | R r -> 
     R (subst_it_r i_subst_it substitution r)

let rec subst_it_a i_subst_it substitution = function
  | Computational ((name,bt),t) -> 
     if Sym.equal name substitution.before then 
       Computational ((name,bt),t) 
     else if SymSet.mem name (IT.free_vars substitution.after) then
       let newname = Sym.fresh () in
       let t' = subst_it_a i_subst_it {before=name; after=IT.sym_ (newname, bt)} t in
       let t'' = subst_it_a i_subst_it substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_it_a i_subst_it substitution t)
  | L l -> L (subst_it_l i_subst_it substitution l)

let subst_its_l i_subst_it = Subst.make_substs (subst_it_l i_subst_it)
let subst_its_r i_subst_it = Subst.make_substs (subst_it_r i_subst_it)
let subst_its_c i_subst_it = Subst.make_substs (subst_it_c i_subst_it)
let subst_its_a i_subst_it = Subst.make_substs (subst_it_a i_subst_it)

let subst_it = subst_it_a
let subst_its = subst_its_a




let (pp_a,pp_l,pp_r,pp_c) =
  let open Pp in
  let rec aux_c i_pp = function
    | Constraint (lc,t) ->
       let op = equals ^^ rangle in
       (LC.pp lc ^^^ op) :: aux_c i_pp t
    | I rt -> [i_pp rt]
  in
  let rec aux_r i_pp = function
    | Resource (re,t) ->
       let op = if !unicode then equals ^^ utf8string "\u{2217}" else minus ^^ star in
       (RE.pp re ^^^ op) :: aux_r i_pp t
    | C c -> aux_c i_pp c
  in
  let rec aux_l i_pp = function
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2200}" else !^"AL" in
       (op ^^^ typ (Sym.pp name) (LS.pp ls) ^^ dot) :: aux_l i_pp t
    | R r -> aux_r i_pp r
  in
  let rec aux_a i_pp = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       (op ^^^ typ (Sym.pp name) (BT.pp bt) ^^ dot) :: aux_a i_pp t
    | L l -> aux_l i_pp l
  in
  let pp_a i_pp t = flow (break 1) (aux_a i_pp t) in
  let pp_l i_pp t = flow (break 1) (aux_l i_pp t) in
  let pp_r i_pp t = flow (break 1) (aux_r i_pp t) in
  let pp_c i_pp t = flow (break 1) (aux_c i_pp t) in
  (pp_a,pp_l,pp_r,pp_c)

let pp = pp_a


let rec count_computational = function
  | Computational (_,t) -> 1 + count_computational t
  | L _ -> 0



let normalise ft : ('rt t) = 
  let rec aux l r c = function
    | AT.Computational ((name,bt),ft) -> Computational ((name,bt), aux l r c ft)
    | AT.Logical ((name,ls),ft) -> aux (l@[(name,ls)]) r c ft
    | AT.Resource (re,ft) -> aux l (r@[re]) c ft
    | AT.Constraint (lc,ft) -> aux l r (c@[lc]) ft
    | AT.I i ->
       L ((List.fold_right mlogical l)
            (R ((List.fold_right mresource r)
                  (C (List.fold_right mconstraint c
                        (I i))))))
  in
  aux [] [] [] ft





let rec unnormalise_c = function
  | Constraint (lc,t) -> AT.Constraint (lc,unnormalise_c t)
  | I rt -> AT.I rt

let rec unnormalise_r = function
  | Resource (re,t) -> AT.Resource (re,unnormalise_r t)
  | C t -> unnormalise_c t

let rec unnormalise_l = function
  | Logical ((name,ls),t) -> AT.Logical ((name,ls),unnormalise_l t)
  | R t -> unnormalise_r t

let rec unnormalise_a = function
  | Computational ((name,bt),t) -> AT.Computational ((name,bt),unnormalise_a t)
  | L t -> unnormalise_l t

let unnormalise = unnormalise_a
