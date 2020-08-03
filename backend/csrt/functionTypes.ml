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

let rec normalise rt : (NFT.t) = 
  let open Tools in
  let rec aux (l_t: NFT.l -> NFT.l) (r_t: NFT.r -> NFT.r) (c_t: NFT.c -> NFT.c) 
              (rt: t) : NFT.t
    =
    match rt with
    | Computational ((name,bt),rt) -> 
       NFT.Computational ((name,bt), normalise rt)
    | Logical ((name,ls),rt) ->
       aux (comp l_t (NFT.mlogical name ls)) r_t c_t rt
    | Resource (re,rt) ->
       aux l_t (comp (NFT.mresource re) r_t) c_t rt
    | Constraint (lc,rt) ->
       aux l_t r_t (comp (NFT.mconstraint lc) c_t) rt
    | Return rt ->
       let rt = RT.normalise rt in
       NFT.L (l_t (NFT.R (r_t (NFT.C (c_t (NFT.Return rt))))))
  in
  aux (fun l -> l) (fun r -> r) (fun c -> c) rt


