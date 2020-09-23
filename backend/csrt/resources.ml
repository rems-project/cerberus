open Pp
open List
module Loc = Locations
module BT = BaseTypes
module IT = IndexTerms
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)

type size = Num.t


type points = 
  { pointer: Sym.t; 
    pointee: Sym.t option; 
    size: size 
  }

type stored_struct =
  { pointer: Sym.t;
    tag: BT.tag;
    size: size;
    members: (BT.member * Sym.t) list 
  }

type t = 
  | Points of points
  | StoredStruct of stored_struct 

type resource = t

let pp_addrmap members =
  flow_map (semi ^^ break 1) 
    (fun (BT.Member m,mvar) -> ampersand ^^ !^m ^^ equals ^^ Sym.pp mvar)
    members

let pp atomic resource = 
  let mparens pp = if atomic then parens pp else pp in
  match resource with
  | Points {size; pointer; pointee} ->
     !^"Points" ^^^ 
       parens (match pointee with 
               | Some v -> Sym.pp pointer ^^ comma ^^ Sym.pp v
               | None -> Sym.pp pointer ^^ comma ^^ !^"uninit"
              )
  | StoredStruct {pointer; tag = Tag s; size; members} ->
     mparens (!^"StoredStruct" ^^^ Sym.pp s ^^^ 
                 parens (Sym.pp pointer ^^ comma ^^ brackets (pp_addrmap members)))


let subst_var subst resource = 
  let subst_membermap subst members = 
    List.map (fun (m,mvar) -> (m,Sym.subst subst mvar)) members in
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (Sym.subst subst s)
       | None -> None
     in
     let pointer = Sym.subst subst p.pointer in
     Points {p with pointer; pointee}
  | StoredStruct s ->
     let pointer = Sym.subst subst s.pointer in
     let members = subst_membermap subst s.members in
     StoredStruct {s with pointer; members}

let subst_vars = Subst.make_substs subst_var


let equal t1 t2 = 
  match t1, t2 with
  | Points p1, Points p2 ->
     Sym.equal p1.pointer p2.pointer &&
     Option.equal Sym.equal p1.pointee p2.pointee &&
     Num.equal p1.size p2.size
  | StoredStruct s1, StoredStruct s2 ->
     Sym.equal s1.pointer s2.pointer &&
     BT.tag_equal s1.tag s2.tag &&
     Num.equal s1.size s2.size &&
     List.equal (fun (member,it) (member',it') -> 
         member = member' && Sym.equal it it'
       ) s1.members s2.members
  | _, _ -> false


let pointer = function
  | Points p -> p.pointer
  | StoredStruct s -> s.pointer

let children = function
  | Points {pointee=None;_} -> []
  | Points {pointee=Some pointee;_} -> [pointee]
  | StoredStruct {members;_} -> map snd members



let vars_in = function
  | Points p -> 
     SymSet.add p.pointer
       (match p.pointee with
        | Some pointee -> SymSet.singleton pointee
        | None -> SymSet.empty)
  | StoredStruct s ->
     List.fold_left (fun s (_,i) -> SymSet.add i s) 
       SymSet.empty s.members
     


let rec unify_memberlist ms ms' res = 
  let open Uni in
  let open Option in
  match ms, ms' with
  | (BT.Member mname,m) :: ms, (BT.Member mname',m') :: ms' 
       when String.equal mname mname' ->
     let* res = unify_sym m m' res in
     unify_memberlist ms ms' res
  | [], [] -> return res
  | _, _ -> fail

let unify r1 r2 res = 
  let open Uni in
  let open Option in
  match r1, r2 with
  | Points p, Points p' when Num.equal p.size p'.size ->
     let* res = unify_sym p.pointer p'.pointer res in
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> unify_sym s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | StoredStruct s, StoredStruct s' ->
     if s.tag = s'.tag && Num.equal s.size s'.size then
       let* res = unify_sym s.pointer s'.pointer res in
       unify_memberlist s.members s'.members res
     else 
       fail
  | _ -> 
     fail


let unify_non_pointer r1 r2 res = 
  let open Uni in
  let open Option in
  match r1, r2 with
  | Points p, Points p' when Num.equal p.size p'.size ->
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> unify_sym s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | StoredStruct s, StoredStruct s' ->
     if s.tag = s'.tag && Num.equal s.size s'.size then
       unify_memberlist s.members s'.members res
     else 
       fail
  | _ -> fail

     

let subst_non_pointer subst resource = 
  let subst_membermap subst members = 
    List.map (fun (m,mvar) -> (m,Sym.subst subst mvar)) members in
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (Sym.subst subst s)
       | None -> None
     in
     Points {p with pointee}
  | StoredStruct s ->
     let members = subst_membermap subst s.members in
     StoredStruct {s with members}



let is_StoredStruct = function
  | StoredStruct s -> Some s 
  | Points _ -> None


type shape = 
  | Points_ of Sym.t * size
  | StoredStruct_ of Sym.t * BT.tag

let shape = function
  | Points p -> Points_ (p.pointer,p.size)
  | StoredStruct s -> StoredStruct_ (s.pointer,s.tag)

let shape_pointer = function
  | Points_ (p,_) -> p
  | StoredStruct_ (p,_) -> p

let match_shape shape resource = 
  match shape, resource with
  | Points_ (pointer,size), Points p' when Num.equal size p'.size -> true
  | StoredStruct_ (pointer,tag), StoredStruct s' -> tag = s'.tag
  | _ -> false

