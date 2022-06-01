open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module AT = ArgumentTypes
module SymSet = Set.Make(Sym)
open Subst



type 'rt c = I of 'rt
           | Constraint of LC.t * info * 'rt c
type 'rt r = C of 'rt c 
           | Resource of (Sym.t * (RET.t * BT.t)) * info * 'rt r 
           | Define of (Sym.t * IT.t) * info * 'rt r
type 'rt a = R of 'rt r 
           | Computational of (Sym.t * BT.t) * info * 'rt a

type 'rt t = 'rt a


let mcomputational (name, bound, oinfo) t = 
  Computational ((name, bound), oinfo, t)
let mconstraint (bound, oinfo) t = 
  Constraint (bound, oinfo, t)
let mresource (bound, oinfo) t = 
  Resource (bound, oinfo, t)
let mdefine ((name, bound), oinfo) t =
  Define ((name, bound), oinfo, t)


let rec subst_c i_subst substitution = function
  | Constraint (lc, oinfo, t) -> 
     let lc = LC.subst substitution lc in
     Constraint (lc, oinfo, subst_c i_subst substitution t)
  | I rt -> 
     I (i_subst substitution rt)

let rec subst_r i_subst substitution = function
  | Resource ((name, (re, bt)), oinfo, t) ->
     let re = RET.subst substitution re in
     let name, t = suitably_alpha_rename_r i_subst substitution.relevant (name, bt) t in
     Resource ((name, (re, bt)), oinfo, subst_r i_subst substitution t)
  | Define ((name, it), info, t) ->
     let it = IT.subst substitution it in
     let name, t = suitably_alpha_rename_r i_subst substitution.relevant (name, IT.bt it) t in
     Define ((name, it), info, subst_r i_subst substitution t)
  | C c -> 
     C (subst_c i_subst substitution c)

and alpha_rename_r i_subst (s, ls) t = 
  let s' = Sym.fresh_same s in
  (s', subst_r i_subst (IT.make_subst [(s, IT.sym_ (s', ls))]) t)

and suitably_alpha_rename_r i_subst syms (s, ls) t =
  if SymSet.mem s syms
  then alpha_rename_r i_subst (s, ls) t
  else (s, t)


let rec subst_a i_subst substitution = function
  | Computational ((name, bt), oinfo, t) -> 
     let name, t = suitably_alpha_rename_a i_subst substitution.relevant (name, bt) t in
     Computational ((name, bt), oinfo, subst_a i_subst substitution t)
  | R r -> 
     R (subst_r i_subst substitution r)

and alpha_rename_a i_subst (s, ls) t = 
  let s' = Sym.fresh_same s in
  (s', subst_a i_subst (IT.make_subst [(s, IT.sym_ (s', ls))]) t)

and suitably_alpha_rename_a i_subst syms (s, ls) t =
  if SymSet.mem s syms
  then alpha_rename_a i_subst (s, ls) t
  else (s, t)


let subst = subst_a




let (pp_a,pp_r,pp_c) =
  let open Pp in
  let rec aux_c i_pp = function
    | Constraint (lc, _oinfo, t) ->
       let op = equals ^^ rangle in
       (LC.pp lc ^^^ op) :: aux_c i_pp t
    | I rt -> [i_pp rt]
  in
  let rec aux_r i_pp = function
    | Resource ((s, (re, _bt)), _oinfo, t) ->
       (!^"let" ^^^ Sym.pp s ^^^ equals ^^^ RET.pp re ^^ semi) :: aux_r i_pp t
    | Define ((s, it), _info, t) ->
       (!^"let" ^^^ Sym.pp s ^^^ equals ^^^ IT.pp it ^^ semi) :: aux_r i_pp t
    | C c -> aux_c i_pp c
  in
  let rec aux_a i_pp = function
    | Computational ((name, bt), _oinfo, t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       (op ^^^ typ (Sym.pp name) (BT.pp bt) ^^ dot) :: aux_a i_pp t
    | R r -> aux_r i_pp r
  in
  let pp_a i_pp t = flow (break 1) (aux_a i_pp t) in
  let pp_r i_pp t = flow (break 1) (aux_r i_pp t) in
  let pp_c i_pp t = flow (break 1) (aux_c i_pp t) in
  (pp_a,pp_r,pp_c)

let pp = pp_a


let rec count_computational = function
  | Computational (_, _, t) -> 1 + count_computational t
  | R _ -> 0



let normalise rt_subst ft : ('rt t) = 
  let rec aux names l r c = function
    | AT.Computational ((name, bt), oinfo, ft) -> 
       Computational ((name,bt), oinfo, aux (name :: names) l r c ft)
    | AT.Define ((name, it), oinfo, ft) ->
       aux (name :: names) l (r@[`Define ((name, it), oinfo)]) c ft
    | AT.Resource ((name, re), oinfo, ft) -> 
       aux (name :: names) l (r@[`Resource ((name, re), oinfo)]) c ft
    | AT.Constraint (lc, oinfo, ft) -> 
       aux names l r (c@[(lc, oinfo)]) ft
    | AT.I i ->
       assert (SymSet.cardinal (SymSet.of_list names) = List.length names);
       let c = List.fold_right mconstraint c (I i) in
       let r = 
         List.fold_right (fun resource_or_define r ->
             match resource_or_define with
             | `Resource (re, oinfo) -> mresource (re, oinfo) r
             | `Define ((name, it), oinfo) -> mdefine ((name, it), oinfo) r
           ) r (C c) in
       R r
  in
  aux [] [] [] [] ft





let rec unnormalise_c = function
  | Constraint (lc, oinfo, t) -> 
     AT.Constraint (lc, oinfo, unnormalise_c t)
  | I rt -> AT.I rt

let rec unnormalise_r = function
  | Resource (re, oinfo, t) -> 
     AT.Resource (re, oinfo, unnormalise_r t)
  | Define ((name, it), info, t) ->
     AT.Define ((name, it), info, unnormalise_r t)
  | C t -> unnormalise_c t

let rec unnormalise_a = function
  | Computational ((name, bt), oinfo, t) -> 
     AT.Computational ((name, bt), oinfo, unnormalise_a t)
  | R t -> unnormalise_r t


let rec r_resource_requests r =
  match r with
  | Resource (resource, info, r) -> resource :: r_resource_requests r
  | _ -> []




let unnormalise = unnormalise_a
