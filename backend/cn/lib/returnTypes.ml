open Locations
module IT = IndexTerms
module LRT = LogicalReturnTypes

type t = Computational of (Sym.t * BaseTypes.t) * info * LRT.t

let mComputational (bound, oinfo) t = Computational (bound, oinfo, t)

let rec subst (substitution : _ Subst.t) at =
  match at with
  | Computational ((name, bt), info, t) ->
    let name, t = LRT.suitably_alpha_rename substitution.relevant name t in
    Computational ((name, bt), info, LRT.subst substitution t)


and alpha_rename_ ~from ~to_ t = (to_, subst (IT.make_rename ~from ~to_) t)

and alpha_rename from t =
  let to_ = Sym.fresh_same from in
  alpha_rename_ ~from ~to_ t


and suitably_alpha_rename syms s t =
  if Sym.Set.mem s syms then
    alpha_rename s t
  else
    (s, t)


let alpha_unique ss = function
  | Computational ((name, bt), oinfo, t) ->
    let t = LRT.alpha_unique (Sym.Set.add name ss) t in
    let name, t = LRT.suitably_alpha_rename ss name t in
    Computational ((name, bt), oinfo, t)


let simp simp_it simp_lc simp_re = function
  | Computational ((s, bt), info, lt) ->
    let s, lt = LRT.alpha_rename s lt in
    Computational ((s, bt), info, LRT.simp simp_it simp_lc simp_re lt)


let binders = function
  | Computational ((s, bt), _, t) ->
    let s, t = LRT.alpha_rename s t in
    (Id.id (Sym.pp_string s), bt) :: LRT.binders t


let map (f : LRT.t -> LRT.t) = function
  | Computational (param, oinfo, t) -> Computational (param, oinfo, f t)


let bound = function Computational ((s, _), _, lrt) -> Sym.Set.add s (LRT.bound lrt)

let pp_aux rt =
  let open Pp in
  match rt with
  | Computational ((name, bt), _info, t) ->
    let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
    (op ^^^ typ (Sym.pp name) (BaseTypes.pp bt) ^^ dot) :: LRT.pp_aux t


let pp rt = Pp.flow (Pp.break 1) (pp_aux rt)

let json = function
  | Computational ((s, bt), _info, t) ->
    let args =
      [ ("symbol", Sym.json s);
        ("basetype", BaseTypes.json bt);
        ("return_type", LRT.json t)
      ]
    in
    `Variant ("Computational", Some (`Assoc args))


let alpha_equivalent rt rt' =
  match (rt, rt') with
  | Computational ((s, bt), _, t), Computational ((s', bt'), _, t') ->
    let new_s = Sym.fresh_same s in
    let _, t = LRT.alpha_rename_ ~to_:new_s ~from:s t in
    let _, t' = LRT.alpha_rename_ ~to_:new_s ~from:s' t' in
    BaseTypes.equal bt bt' && LRT.alpha_equivalent t t'


open Cerb_frontend.Pp_ast

let dtree = function
  | Computational ((s, _bt), _, lrt) ->
    Dnode (pp_ctor "Computational", [ Dleaf (Sym.pp s); LRT.dtree lrt ])
