open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type 'i t =
  | Define of (Sym.t * IT.t) * info * 'i t
  | Resource of (Sym.t * (RET.t * BT.t)) * info * 'i t
  | Constraint of LC.t * info * 'i t
  | I of 'i

let mDefine (name, it, info) t = Define ((name, it), info, t)
let mResource (bound, info) t = Resource (bound, info, t)
let mConstraint (bound, info) t = Constraint (bound, info, t)

let mDefines defs t = List.fold_right mDefine defs t
let mResources ress t = List.fold_right mResource ress t
let mConstraints cons t = List.fold_right mConstraint cons t



let rec subst i_subst =
  let rec aux (substitution: _ Subst.t) at =
    match at with
    | Define ((name, it), info, t) ->
       let it = IT.subst substitution it in
       let name, t = suitably_alpha_rename i_subst substitution.relevant name t in
       Define ((name, it), info, aux substitution t)
    | Resource ((name, (re, bt)),((loc, _) as info), t) ->
       let re = RET.subst substitution re in
       let name, t = suitably_alpha_rename i_subst substitution.relevant name t in
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

and alpha_rename i_subst s t =
  let s' = Sym.fresh_same s in
  (s', subst i_subst (IT.make_rename ~from:s ~to_:s') t)

and suitably_alpha_rename i_subst syms s t =
  Pp.debug 8 (lazy (Pp.item __FUNCTION__ (Pp.list Sym.pp_debug (SymSet.fold (List.cons) syms []))));
  Pp.debug 8 (lazy (Pp.item "bound" (Sym.pp_debug s)));
  if SymSet.mem s syms
  then (Pp.debug 8 (lazy (Pp.string "renaming..")); alpha_rename i_subst s t)
  else (Pp.debug 8 (lazy (Pp.string "skipping.."));(s, t))



let simp i_subst simp_i simp_it simp_lc simp_re =
  let rec aux = function
    | Define ((s, it), info, t) ->
       let it = simp_it it in
       let s, t = alpha_rename i_subst s t in
       Define ((s, it), info, aux t)
    | Resource ((s, (re, bt)), info, t) ->
       let re = simp_re re in
       let s, t = alpha_rename i_subst s t in
       Resource ((s, (re, bt)), info, aux t)
    | Constraint (lc, info, t) ->
       let lc = simp_lc lc in
       Constraint (lc, info, aux t)
    | I i ->
       let i = simp_i i in
       I i
  in
  aux


open Pp

let rec pp_aux i_pp = function
  | Define ((name, it), _info, t) ->
     group (!^"let" ^^^ (Sym.pp name) ^^^ equals ^^^ IT.pp it ^^ semi) :: pp_aux i_pp t
  | Resource ((name, (re, _bt)), _info, t) ->
     group (!^"take" ^^^ (Sym.pp_debug name) ^^^ equals ^^^ RET.pp re ^^ semi) :: pp_aux i_pp t
  | Constraint (lc, _info, t) ->
     let op = equals ^^ rangle () in
     group (LC.pp lc ^^^ op) :: pp_aux i_pp t
  | I i ->
     [i_pp i]


let pp i_pp ft =
  flow (break 1) (pp_aux i_pp ft)


let rec get_return = function
  | Define (_, _, ft) -> get_return ft
  | Resource (_, _, ft) -> get_return ft
  | Constraint (_, _, ft) -> get_return ft
  | I rt -> rt


module LRT = LogicalReturnTypes
module RT = ReturnTypes


let alpha_unique ss =
  let rename_if ss = suitably_alpha_rename RT.subst ss in
  let rec f ss at =
    match at with
    | Define ((name, it), info, t) ->
       let name, t = rename_if ss name t in
       let t = f (SymSet.add name ss) t in
       Define ((name, it), info, t)
    | Resource ((name, (re, bt)), info, t) ->
       let name, t = rename_if ss name t in
       let t = f (SymSet.add name ss) t in
       Resource ((name, (re, bt)), info, f ss t)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I i -> I (RT.alpha_unique ss i)
  in
  f ss


let binders i_binders i_subst =
  let rec aux = function
    | Define ((s, it), (loc, _), t) ->
       let (s, t) = alpha_rename i_subst s t in
       (Id.id (Sym.pp_string s), IT.bt it) :: aux t
    | Resource ((s, (re, bt)), (loc, _), t) ->
       let (s, t) = alpha_rename i_subst s t in
       (Id.id (Sym.pp_string s), bt) :: aux t
    | Constraint (lc, _, t) ->
       aux t
    | I i ->
       i_binders i
  in
  aux



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

let rec map (f : 'i -> 'j) (at : 'i t) : 'j t =
  match at with
  | Define (bound, info, at) ->
     Define (bound, info, map f at)
  | Resource (bound, info, at) ->
     Resource (bound, info, map f at)
  | Constraint (lc, info, at) ->
     Constraint (lc, info, map f at)
  | I i ->
     I (f i)



let rec r_resource_requests r =
  match r with
  | Define (_, _, t) ->
     r_resource_requests t
  | Resource (resource, info, t) ->
     resource :: r_resource_requests t
  | Constraint (_, _, t) ->
     r_resource_requests t
  | I _ ->
     []






type packing_ft = IT.t t
type lft = LogicalReturnTypes.t t


let rec has_resource (f : 'a -> bool) (at : 'a t) =
  match at with
  | I x -> f x
  | Resource _ -> true
  | Define (_, _, at) -> has_resource f at
  | Constraint (_, _, at) -> has_resource f at



open Cerb_frontend.Pp_ast


let dtree dtree_i =
  let rec aux = function
  | Define ((s, it), _, t) ->
     Dnode (pp_ctor "Define", [Dleaf (Sym.pp s); IT.dtree it; aux t])
  | Resource ((s, (rt, bt)), _, t) ->
     Dnode (pp_ctor "Resource", [Dleaf (Sym.pp s); RET.dtree rt; Dleaf (BT.pp bt); aux t])
  | Constraint (lc, _, t) ->
     Dnode (pp_ctor "Constraint", [LC.dtree lc; aux t])
  | I i ->
     Dnode (pp_ctor "I", [dtree_i i])
  in
  aux
