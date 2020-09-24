open Pp
module Loc = Locations
module BT = BaseTypes
module IT = IndexTerms
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)

type size = Num.t


type points = 
  { pointer: IT.t; 
    pointee: IT.t option; 
    size: size 
  }

type stored_struct =
  { pointer: IT.t;
    tag: BT.tag;
    size: size;
    members: (BT.member * IT.t) list 
  }

type t = 
  | Points of points

type resource = t

let pp_addrmap members =
  flow_map (semi ^^ break 1) 
    (fun (BT.Member m,mvar) -> ampersand ^^ !^m ^^ equals ^^ IT.pp false mvar)
    members

let pp atomic resource = 
  match resource with
  | Points {size; pointer; pointee} ->
     !^"Points" ^^^ 
       parens (match pointee with 
               | Some v -> IT.pp false pointer ^^ comma ^^ IT.pp false v
               | None -> IT.pp false pointer ^^ comma ^^ !^"uninit"
              )



let subst_var (subst: (Sym.t,IT.t) Subst.t) resource = 
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (IT.subst_var subst s)
       | None -> None
     in
     let pointer = IT.subst_var subst p.pointer in
     Points {p with pointer; pointee}


let subst_vars = Subst.make_substs subst_var


let equal t1 t2 = 
  match t1, t2 with
  | Points p1, Points p2 ->
     IT.equal p1.pointer p2.pointer &&
     Option.equal IT.equal p1.pointee p2.pointee &&
     Num.equal p1.size p2.size


let pointer = function
  | Points p -> p.pointer

let children = function
  | Points {pointee=None;_} -> []
  | Points {pointee=Some pointee;_} -> [pointee]

let vars_in = function
  | Points p -> 
     SymSet.union (IT.vars_in p.pointer)
       (match p.pointee with
        | Some pointee -> IT.vars_in pointee
        | None -> SymSet.empty)



let rec unify_memberlist ms ms' res = 
  let open Option in
  match ms, ms' with
  | (BT.Member mname,m) :: ms, (BT.Member mname',m') :: ms' 
       when String.equal mname mname' ->
     let* res = IT.unify m m' res in
     unify_memberlist ms ms' res
  | [], [] -> return res
  | _, _ -> fail

let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Points p, Points p' when Num.equal p.size p'.size ->
     let* res = IT.unify p.pointer p'.pointer res in
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> IT.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | _ -> 
     fail


let unify_non_pointer r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Points p, Points p' when Num.equal p.size p'.size ->
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> IT.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | _ -> fail

     

let subst_non_pointer subst resource = 
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (IT.subst_var subst s)
       | None -> None
     in
     Points {p with pointee}



type shape = 
  | Points_ of IT.t * size

let shape = function
  | Points p -> Points_ (p.pointer,p.size)

let shape_pointer = function
  | Points_ (p,_) -> p

let match_shape shape resource = 
  match shape, resource with
  | Points_ (pointer,size), Points p' when Num.equal size p'.size -> true
  | _ -> false

