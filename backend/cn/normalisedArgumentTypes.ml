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



let rec subst_c i_subst substitution = function
  | Constraint (lc, t) -> 
     Constraint (LC.subst substitution lc, 
                 subst_c i_subst substitution t)
  | I rt -> 
     I (i_subst substitution rt)

let rec subst_r i_subst substitution = function
  | Resource (re, t) ->
     Resource (RE.subst substitution re, 
               subst_r i_subst substitution t)
  | C c -> 
     C (subst_c i_subst substitution c)

let rec subst_l i_subst substitution = function
  | Logical ((name, ls), t) -> 
     let name' = Sym.fresh () in
     let t' = subst_l i_subst [(name, IT.sym_ (name', ls))] t in
     let t'' = subst_l i_subst substitution t' in
     Logical ((name', ls), t'')
  | R r -> 
     R (subst_r i_subst substitution r)

let rec subst_a i_subst substitution = function
  | Computational ((name,bt),t) -> 
     let name' = Sym.fresh () in
     let t' = subst_a i_subst [(name, IT.sym_ (name', bt))] t in
     let t'' = subst_a i_subst substitution t' in
     Computational ((name',bt),t'')
  | L l -> 
     L (subst_l i_subst substitution l)


let subst = subst_a




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
