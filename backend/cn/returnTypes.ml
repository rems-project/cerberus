open Locations
module SymSet = Set.Make(Sym)
module IT = IndexTerms

module LRT = LogicalReturnTypes

type t = Computational of (Sym.t * BaseTypes.t) * info * LRT.t




let mComputational (bound, oinfo) t =
  Computational (bound, oinfo, t)










let rec subst (substitution: IT.t Subst.t) at =
  match at with
  | Computational ((name, bt), ((loc, _) as info), t) ->
     (* TODO Check this location *)
     let name, t = LRT.suitably_alpha_rename substitution.relevant (name, bt, loc) t in
     Computational ((name, bt), info, LRT.subst substitution t)

and alpha_rename_ s' loc (s, ls) t =
  (s', subst (IT.make_subst [(s, IT.sym_ (s', ls, loc))]) t)

and alpha_rename (s, ls, loc) t =
  let s' = Sym.fresh_same s in
  alpha_rename_ s' loc (s, ls) t

and suitably_alpha_rename syms (s, ls, loc) t =
  if SymSet.mem s syms
  then alpha_rename (s, ls, loc) t
  else (s, t)


let alpha_unique ss = function
  | Computational ((name, bt),((loc, _) as oinfo), t) ->
    let t = LRT.alpha_unique (SymSet.add name ss) t in
    let (name, t) = LRT.suitably_alpha_rename ss (name, bt, loc) t in
    Computational ((name, bt), oinfo, t)


let simp simp_it simp_lc simp_re = function
  | Computational ((s, bt),((loc, _) as info), lt) ->
     let s, lt = LRT.alpha_rename (s, bt, loc) lt in
     Computational ((s, bt), info, LRT.simp simp_it simp_lc simp_re lt)


let binders = function
  | Computational ((s, bt), (loc, _), t) ->
     (* TODO Check this location *)
     let (s, t) = LRT.alpha_rename (s, bt, loc) t in
     (Id.id (Sym.pp_string s), bt) :: LRT.binders t


let map (f : LRT.t -> LRT.t) = function
  | Computational (param, oinfo, t) -> Computational (param, oinfo, f t)


let bound = function
  | Computational ((s, _), _, lrt) ->
     SymSet.add s (LRT.bound lrt)



let pp_aux rt =
  let open Pp in
  match rt with
  | Computational ((name, bt), oinfo, t) ->
     let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
     (op ^^^ typ (Sym.pp name) (BaseTypes.pp bt) ^^ dot) :: LRT.pp_aux t

let pp rt =
  Pp.flow (Pp.break 1) (pp_aux rt)



let json = function
  | Computational ((s, bt), oinfo, t) ->
     let args = [
         ("symbol", Sym.json s);
         ("basetype", BaseTypes.json bt);
         ("return_type", LRT.json t);
       ]
     in
     `Variant ("Computational", Some (`Assoc args))



let alpha_equivalent rt rt' =
  match rt, rt' with
  | Computational ((s, bt), _, t),
    Computational ((s', bt'), _, t') ->
     let new_s = Sym.fresh_same s in
     let loc = Cerb_location.other __FUNCTION__ in
     let _, t = LRT.alpha_rename_ new_s loc (s, bt) t in
     let _, t' = LRT.alpha_rename_ new_s loc (s', bt') t' in
     BaseTypes.equal bt bt' && LRT.alpha_equivalent t t'




open Cerb_frontend.Pp_ast


let dtree = function
  | Computational ((s, bt), _, lrt) ->
     Dnode (pp_ctor "Computational", [Dleaf (Sym.pp s); LRT.dtree lrt])

