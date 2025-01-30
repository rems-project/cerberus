open Locations
module BT = BaseTypes
module RT = Request
module IT = IndexTerms
module LC = LogicalConstraints

type t =
  | Define of (Sym.t * IT.t) * info * t
  | Resource of (Sym.t * (RT.t * BT.t)) * info * t
  | Constraint of LogicalConstraints.t * info * t
  | I

let mDefine (name, bound, info) t = Define ((name, bound), info, t)

let mResource (bound, info) t = Resource (bound, info, t)

let mConstraint (bound, info) t = Constraint (bound, info, t)

let mDefines = List.fold_right mDefine

let mResources = List.fold_right mResource

let mConstraints = List.fold_right mConstraint

let rec subst (substitution : _ Subst.t) lrt =
  match lrt with
  | Define ((name, it), info, t) ->
    let it = IT.subst substitution it in
    let name, t = suitably_alpha_rename substitution.relevant name t in
    Define ((name, it), info, subst substitution t)
  | Resource ((name, (re, bt)), info, t) ->
    let re = RT.subst substitution re in
    let name, t = suitably_alpha_rename substitution.relevant name t in
    let t = subst substitution t in
    Resource ((name, (re, bt)), info, t)
  | Constraint (lc, info, t) ->
    let lc = LogicalConstraints.subst substitution lc in
    let t = subst substitution t in
    Constraint (lc, info, t)
  | I -> I


and alpha_rename_ ~from ~to_ t =
  ( to_,
    if Sym.equal from to_ then
      t
    else
      subst (IT.make_rename ~from ~to_) t )


and alpha_rename from t =
  let to_ = Sym.fresh_same from in
  alpha_rename_ ~from ~to_ t


and suitably_alpha_rename syms s t =
  if Sym.Set.mem s syms then
    alpha_rename s t
  else
    (s, t)


let rec bound = function
  | Define ((s, _), _, lrt) -> Sym.Set.add s (bound lrt)
  | Resource ((s, _), _, lrt) -> Sym.Set.add s (bound lrt)
  | Constraint (_, _, lrt) -> bound lrt
  | I -> Sym.Set.empty


let alpha_unique ss =
  let rec f ss = function
    | Resource ((name, (re, bt)), info, t) ->
      let t = f (Sym.Set.add name ss) t in
      let name, t = suitably_alpha_rename ss name t in
      Resource ((name, (re, bt)), info, t)
    | Define ((name, it), info, t) ->
      let t = f (Sym.Set.add name ss) t in
      let name, t = suitably_alpha_rename ss name t in
      Define ((name, it), info, t)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I -> I
  in
  f ss


let binders =
  let here = Locations.other __LOC__ in
  let rec aux = function
    | Define ((s, it), _, t) ->
      let s, t = alpha_rename s t in
      (Id.make here (Sym.pp_string s), IT.get_bt it) :: aux t
    | Resource ((s, (_, bt)), _, t) ->
      let s, t = alpha_rename s t in
      (Id.make here (Sym.pp_string s), bt) :: aux t
    | Constraint (_, _, t) -> aux t
    | I -> []
  in
  aux


let free_vars lrt =
  let rec f = function
    | Define ((nm, it), _, t) -> Sym.Set.union (IT.free_vars it) (Sym.Set.remove nm (f t))
    | Resource ((nm, (re, _)), _, t) ->
      Sym.Set.union (RT.free_vars re) (Sym.Set.remove nm (f t))
    | Constraint (lc, _, t) -> Sym.Set.union (LogicalConstraints.free_vars lc) (f t)
    | I -> Sym.Set.empty
  in
  f lrt


let simp simp_it simp_lc simp_re =
  let rec aux = function
    | Define ((s, it), info, t) ->
      let it = simp_it it in
      let s, t = alpha_rename s t in
      Define ((s, it), info, aux t)
    | Resource ((s, (re, bt)), info, t) ->
      let re = simp_re re in
      let s, t = alpha_rename s t in
      Resource ((s, (re, bt)), info, aux t)
    | Constraint (lc, info, t) ->
      let lc = simp_lc lc in
      Constraint (lc, info, aux t)
    | I -> I
  in
  aux


let rec pp_aux lrt =
  let open Pp in
  match lrt with
  | Define ((name, it), _info, t) ->
    group (!^"let" ^^^ Sym.pp name ^^^ equals ^^^ IT.pp it ^^ semi) :: pp_aux t
  | Resource ((name, (re, _bt)), _info, t) ->
    group (!^"take" ^^^ Sym.pp name ^^^ equals ^^^ RT.pp re ^^ semi) :: pp_aux t
  | Constraint (lc, _info, t) ->
    let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
    group (LogicalConstraints.pp lc ^^^ op) :: pp_aux t
  | I -> [ !^"I" ]


let pp rt = Pp.flow (Pp.break 1) (pp_aux rt)

let rec json = function
  | Define ((s, it), _info, t) ->
    let args =
      [ ("symbol", Sym.json s); ("term", IT.json it); ("return_type", json t) ]
    in
    `Variant ("Define", Some (`Assoc args))
  | Resource ((s, (r, _bt)), _info, t) ->
    let args =
      [ ("symbol", Sym.json s); ("resource", RT.json r); ("return_type", json t) ]
    in
    `Variant ("Resource", Some (`Assoc args))
  | Constraint (lc, _info, t) ->
    let args = [ ("constraint", LogicalConstraints.json lc); ("return_type", json t) ] in
    `Variant ("Constraint", Some (`Assoc args))
  | I -> `Variant ("I", None)


let rec alpha_equivalent lrt lrt' =
  match (lrt, lrt') with
  | Define ((s, it), _, lrt), Define ((s', it'), _, lrt') ->
    let new_s = if Sym.equal s s' then s else Sym.fresh_same s in
    let _, lrt = alpha_rename_ ~to_:new_s ~from:s lrt in
    let _, lrt' = alpha_rename_ ~to_:new_s ~from:s' lrt' in
    IT.equal it it' && alpha_equivalent lrt lrt'
  | Resource ((s, (re, bt)), _, lrt), Resource ((s', (re', bt')), _, lrt') ->
    let new_s = if Sym.equal s s' then s else Sym.fresh_same s in
    let _, lrt = alpha_rename_ ~to_:new_s ~from:s lrt in
    let _, lrt' = alpha_rename_ ~to_:new_s ~from:s' lrt' in
    RT.alpha_equivalent re re' && BT.equal bt bt' && alpha_equivalent lrt lrt'
  | Constraint (lc, _, lrt), Constraint (lc', _, lrt') ->
    LC.alpha_equivalent lc lc' && alpha_equivalent lrt lrt'
  | I, I -> true
  | _ -> false


open Cerb_frontend.Pp_ast
open Pp

let rec dtree = function
  | Define ((s, it), _, t) ->
    Dnode (pp_ctor "Define", [ Dleaf (Sym.pp s); IT.dtree it; dtree t ])
  | Resource ((s, (rt, bt)), _, t) ->
    Dnode
      (pp_ctor "Resource", [ Dleaf (Sym.pp s); RT.dtree rt; Dleaf (BT.pp bt); dtree t ])
  | Constraint (lc, _, t) -> Dnode (pp_ctor "Constraint", [ LC.dtree lc; dtree t ])
  | I -> Dleaf !^"I"


let rec contains_c = function
  | Define (_, _, t) -> contains_c t
  | Resource (_, _, t) -> contains_c t
  | Constraint (_, _, _) -> true
  | I -> false
