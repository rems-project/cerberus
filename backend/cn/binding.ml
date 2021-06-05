module L = Local
module LRT = LogicalReturnTypes
module RT = ReturnTypes
open L



let rec bind_logical (delta : L.t) (lrt : LRT.t) : L.t = 
  match lrt with
  | Logical ((s, ls), rt) ->
     let s' = Sym.fresh () in
     let rt' = LRT.subst_var {before=s; after=s'} rt in
     bind_logical (add_l s' ls delta) rt'
  | Resource (re, rt) -> bind_logical (add_r re delta) rt
  | Constraint (lc, rt) -> bind_logical (add_c lc delta) rt
  | I -> delta

let bind_computational (delta : L.t) (name : Sym.t) (rt : RT.t) : L.t =
  let Computational ((s, bt), rt) = rt in
  let s' = Sym.fresh () in
  let rt' = LRT.subst_var {before = s; after = s'} rt in
  let delta' = add_a name (bt, s') (add_l s' bt delta) in
  bind_logical delta' rt'


let bind (name : Sym.t) (rt : RT.t) : L.t =
  bind_computational L.empty name rt

let bind_logically (rt : RT.t) : ((BT.t * Sym.t) * L.t) =
  let Computational ((s, bt), rt) = rt in
  let s' = Sym.fresh () in
  let rt' = LRT.subst_var {before = s; after = s'} rt in
  let delta = add_l s' bt L.empty in
  let delta' = bind_logical delta rt' in
  ((bt, s'), delta')
