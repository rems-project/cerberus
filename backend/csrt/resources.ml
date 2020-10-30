open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

type size = Z.t

type uninit = {pointer: IndexTerms.t; size: size}
type points = {pointer: IndexTerms.t; pointee: Sym.t; size: size}

type t = 
  | Uninit of uninit
  | Points of points

type resource = t

let pp = function
  | Uninit {pointer; size} ->
     !^"Uninit" ^^ parens (IndexTerms.pp pointer ^^ comma ^^ Z.pp size)
  | Points {pointer; pointee; size} ->
     !^"Points" ^^ 
       parens (IndexTerms.pp pointer ^^ comma ^^ Sym.pp pointee ^^ 
                 comma ^^ Z.pp size)



let subst_var (subst: (Sym.t,Sym.t) Subst.t) = function
  | Uninit {pointer; size} ->
     let pointer = IndexTerms.subst_var subst pointer in
     Uninit {pointer; size}
  | Points {pointer; pointee; size} -> 
     let pointer = IndexTerms.subst_var subst pointer in
     let pointee = Sym.subst subst pointee in
     Points {pointer; pointee; size}


let subst_vars = Subst.make_substs subst_var


let equal t1 t2 = 
  match t1, t2 with
  | Uninit u1, Uninit u2 ->
     IndexTerms.equal u1.pointer u2.pointer &&
     Z.equal u1.size u2.size
  | Points p1, Points p2 ->
     IndexTerms.equal p1.pointer p2.pointer &&
     Sym.equal p1.pointee p2.pointee &&
     Z.equal p1.size p2.size
  | _, _ -> false


let pointer = function
  | Uninit u -> u.pointer
  | Points p -> p.pointer

let size = function
  | Uninit u -> u.size
  | Points p -> p.size

let fp resource = (pointer resource, size resource)

let vars_in = function
  | Uninit p -> IndexTerms.vars_in p.pointer
  | Points p -> SymSet.add p.pointee (IndexTerms.vars_in p.pointer)


let set_pointer re pointer = 
  match re with
  | Uninit u -> Uninit { u with pointer }
  | Points p -> Points { p with pointer }


(* requires equality on index terms (does not try to unify them) *)
let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Uninit u, Uninit u' 
       when Z.equal u.size u'.size && IndexTerms.equal u.pointer u'.pointer ->
     return res
  | Points p, Points p' 
       when Z.equal p.size p'.size && IndexTerms.equal p.pointer p'.pointer ->
     Uni.unify_sym p.pointee p'.pointee res
  | _ -> 
     fail


let subst_non_pointer subst = function
  | Uninit u -> Uninit u
  | Points p -> Points {p with pointee = Sym.subst subst p.pointee}





let input = function
  | Uninit u -> IndexTerms.vars_in u.pointer
  | Points p -> IndexTerms.vars_in p.pointer

let output = function
  | Uninit _ -> SymSet.empty
  | Points p -> SymSet.singleton p.pointee



