open Pp
module Loc = Locations
module BT = BaseTypes
module IT = IndexTerms
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)

type size = Num.t

type uninit = {pointer: IT.t; size: size}
type points = {pointer: IT.t; pointee: IT.t; size: size}

type t = 
  | Uninit of uninit
  | Points of points

type resource = t

let pp = function
  | Uninit {pointer; size} ->
     !^"Uninit" ^^^ parens (IT.pp pointer ^^ comma ^^^ Num.pp size)
  | Points {pointer; pointee; size} ->
     !^"Points" ^^^ 
       parens (IT.pp pointer ^^ comma ^^^ IT.pp pointee ^^ comma ^^^ Num.pp size)



let subst_var (subst: (Sym.t,IT.t) Subst.t) = function
  | Uninit {pointer; size} ->
     let pointer = IT.subst_var subst pointer in
     Uninit {pointer; size}
  | Points {pointer; pointee; size} -> 
     let pointer = IT.subst_var subst pointer in
     let pointee = IT.subst_var subst pointee in
     Points {pointer; pointee; size}


let subst_vars = Subst.make_substs subst_var


let equal t1 t2 = 
  match t1, t2 with
  | Uninit u1, Uninit u2 ->
     IT.equal u1.pointer u2.pointer &&
     Num.equal u1.size u2.size
  | Points p1, Points p2 ->
     IT.equal p1.pointer p2.pointer &&
     IT.equal p1.pointee p2.pointee &&
     Num.equal p1.size p2.size
  | _, _ -> false


let pointer = function
  | Uninit u -> u.pointer
  | Points p -> p.pointer

let size = function
  | Uninit u -> u.size
  | Points p -> p.size

let fp resource = (pointer resource, size resource)

let vars_in = function
  | Uninit p -> IT.vars_in p.pointer
  | Points p -> SymSet.union (IT.vars_in p.pointer) (IT.vars_in p.pointee)


let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Uninit u, Uninit u' when Num.equal u.size u'.size ->
     IT.unify u.pointer u'.pointer res
  | Points p, Points p' when Num.equal p.size p'.size ->
     let* res = IT.unify p.pointer p'.pointer res in
     let* res = IT.unify p.pointee p'.pointee res in
     return res
  | _ -> 
     fail


let unify_non_pointer r1 r2 res = 
  match r1, r2 with
  | Uninit u, Uninit u' when Num.equal u.size u'.size ->
     Option.return res
  | Points p, Points p' when Num.equal p.size p'.size ->
     IT.unify p.pointee p'.pointee res
  | _ -> 
     Option.fail


let subst_non_pointer subst = function
  | Uninit u -> Uninit u
  | Points p -> Points {p with pointee = IT.subst_var subst p.pointee}



