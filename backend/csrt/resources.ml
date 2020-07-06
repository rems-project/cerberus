open Option
open Pp
open List
module Loc = Locations
module BT = BaseTypes
module IT = IndexTerms
module CF = Cerb_frontend




type points = 
  { pointer: IT.t; 
    pointee: IT.t option; 
    typ: CF.Ctype.ctype;
    size: Num.t 
  }

type stored_struct =
  { pointer: IT.t;
    tag: BT.tag;
    size: Num.t;
    members: (BT.member * IT.t) list }

type t = 
  | Points of points
  | StoredStruct of stored_struct 

let pp_addrmap members =
  flow_map (semi ^^ break 1) 
    (fun (BT.Member m,mvar) -> ampersand ^^ !^m ^^ equals ^^ IT.pp true mvar)
    members

let pp atomic resource = 
  let mparens pp = if atomic then parens pp else pp in
  match resource with
  | Points {typ; size; pointer; pointee} ->
     !^"Points" ^^^ 
       parens (pp_ctype typ ^^ comma ^^
                 match pointee with 
                 | Some v -> IT.pp true pointer ^^ comma ^^ IT.pp true v
                 | None -> IT.pp true pointer ^^ comma ^^ !^"uninit")
  | StoredStruct {pointer; tag = Tag s; size; members} ->
     mparens (!^"StoredStruct" ^^^ Sym.pp s ^^^ 
                 parens (IT.pp true pointer ^^ comma ^^ brackets (pp_addrmap members)))


let subst_var subst resource = 
  let subst_membermap subst members = 
    List.map (fun (m,mvar) -> (m,IT.subst_var subst mvar)) members in
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (IT.subst_var subst s)
       | None -> None
     in
     let pointer = IT.subst_var subst p.pointer in
     Points {p with pointer; pointee}
  | StoredStruct s ->
     let pointer = IT.subst_var subst s.pointer in
     let members = subst_membermap subst s.members in
     StoredStruct {s with pointer; members}

let subst_vars = Subst.make_substs subst_var


let instantiate_struct_member subst resource =
  let subst_membermap subst members = 
    List.map (fun (m,mvar) -> (m,IT.instantiate_struct_member subst mvar)) members in
  match resource with
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (IT.instantiate_struct_member subst s)
       | None -> None
     in
     let pointer = IT.instantiate_struct_member subst p.pointer in
     Points {p with pointer; pointee}
  | StoredStruct s ->
     let pointer = IT.instantiate_struct_member subst s.pointer in
     let members = subst_membermap subst s.members in
     StoredStruct {s with pointer; members}


let type_equal env t1 t2 = t1 = t2

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)




let associated = function
  | Points p -> p.pointer
  | StoredStruct s -> s.pointer



let rec unify_memberlist ms ms' res = 
  match ms, ms' with
  | (BT.Member mname,m) :: ms, (BT.Member mname',m') :: ms' 
       when String.equal mname mname' ->
     let* res = IT.unify m m' res in
     unify_memberlist ms ms' res
  | [], [] -> return res
  | _, _ -> fail

let unify r1 r2 res = 
  match r1, r2 with
  | Points p, Points p' 
       when CF.Ctype.ctypeEqual p.typ p'.typ && Num.equal p.size p'.size ->
     let* res = IT.unify p.pointer p'.pointer res in
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> IT.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | StoredStruct s, StoredStruct s' ->
     if s.tag = s'.tag && Num.equal s.size s'.size then
       let* res = IT.unify s.pointer s'.pointer res in
       unify_memberlist s.members s'.members res
     else 
       fail
  | _ -> fail
