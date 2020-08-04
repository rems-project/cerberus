open Subst

module RT = ReturnTypes
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)

type t = 
  | Computational of (Sym.t * BT.t) * t
  | Logical of (Sym.t * LS.t) * t
  | Resource of RE.t * t
  | Constraint of LC.t * t
  | Return of ReturnTypes.t



let mcomputational name bound t = 
  Computational ((name,bound),t)
let mlogical name bound t = 
  Logical ((name,bound),t)
let mconstraint bound t = 
  Constraint (bound,t)
let mresource bound t = 
  Resource (bound,t)



let rec subst_var substitution = function
  | Return t -> Return (ReturnTypes.subst_var substitution t)
  | Computational ((name,bt),t) -> 
     if name = substitution.s then 
       Computational ((name,bt),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var {s=name; swith=IT.S newname} t in
       let t'' = subst_var substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_var substitution t)
  | Logical ((name,ls),t) -> 
     if name = substitution.s then 
       Logical ((name,ls),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var {s=name; swith=IT.S newname} t in
       let t'' = subst_var substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst_var substitution t in
       Logical ((name,ls),t')
  | Resource (re,t) -> 
     let re = RE.subst_var substitution re in
     let t = subst_var substitution t in
     Resource (re,t)
  | Constraint (lc,t) -> 
     let lc = LC.subst_var substitution lc in
     let t = subst_var substitution t in
     Constraint (lc,t)

let rec instantiate_struct_member subst ft =
  match ft with
  | Return rt -> 
     Return (RT.instantiate_struct_member subst rt)
  | Computational ((name,bound),t) -> 
     Computational ((name,bound),instantiate_struct_member subst t)
  | Logical ((name,bound),t) -> 
     Logical ((name,bound),instantiate_struct_member subst t)
  | Resource (bound,t) -> 
     Resource (RE.instantiate_struct_member subst bound, 
               instantiate_struct_member subst t)
  | Constraint (bound,t) -> 
     Constraint (LC.instantiate_struct_member subst bound, 
                 instantiate_struct_member subst t)


let pp rt = 
  let open Pp in
  let rec aux = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux t
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2200}" else !^"AL" in
       (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux t
    | Resource (re,t) ->
       let op = if !unicode then equals ^^ utf8string "\u{2217}" else minus ^^ star in
       (RE.pp false re ^^^ op) :: aux t
    | Constraint (lc,t) ->
       let op = equals ^^ rangle in
       (LC.pp false lc ^^^ op) :: aux t
    | Return rt -> 
       [RT.pp rt]
  in
  flow (break 1) (aux rt)



let rec count_computational = function
  | Computational (_,ft) -> 
     1 + count_computational ft
  | Logical (_,ft) 
    | Resource (_,ft)
    | Constraint (_,ft) -> 
     count_computational ft
  | Return _ -> 0


module NFT = NFunctionTypes

let normalise ft : (NFT.t) = 
  let rec aux l r c = function
    | Computational ((name,bt),ft) -> NFT.Computational ((name,bt), aux l r c ft)
    | Logical ((name,ls),ft) -> aux (l@[(name,ls)]) r c ft
    | Resource (re,ft) -> aux l (r@[re]) c ft
    | Constraint (lc,ft) -> aux l r (c@[lc]) ft
    | Return rt ->
       (NFT.L ((List.fold_right NFT.mlogical l)
                 (NFT.R ((List.fold_right NFT.mresource r)
                           (NFT.C (List.fold_right NFT.mconstraint c
                             (NFT.Return (RT.normalise rt))))))))
  in
  aux [] [] [] ft





let rec unnormalise_c = function
  | NFT.Constraint (lc,t) -> Constraint (lc,unnormalise_c t)
  | NFT.Return rt -> Return (RT.unnormalise rt)

let rec unnormalise_r = function
  | NFT.Resource (re,t) -> Resource (re,unnormalise_r t)
  | NFT.C t -> unnormalise_c t

let rec unnormalise_l = function
  | NFT.Logical ((name,ls),t) -> Logical ((name,ls),unnormalise_l t)
  | NFT.R t -> unnormalise_r t

let rec unnormalise_a = function
  | NFT.Computational ((name,bt),t) -> Computational ((name,bt),unnormalise_a t)
  | NFT.L t -> unnormalise_l t

let unnormalise = unnormalise_a
