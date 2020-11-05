module CF = Cerb_frontend
open TypeErrors
open Resultat
open Pp

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms

open Memory_aux

open Environment



let for_fp_filter (loc: Loc.t) {local;global} (pointer_it, size) =
  fun name re ->
  if Z.equal (RE.size re) size then 
    let* holds = Solver.equal loc {local;global} pointer_it (RE.pointer re) in
    return holds
  else 
    return false

let for_fp (loc: Loc.t) {local;global} (pointer_it, size) 
    : ((Sym.t * RE.t) option) m = 
  let* points = 
    Local.filterM (fun name vb ->
        match vb with 
        | VariableBinding.Resource re -> 
           let* holds = for_fp_filter loc {local; global} (pointer_it, size) name re in
           return (if holds then Some (name, re) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points

let for_fp_used (loc: Loc.t) {local;global} (pointer_it, size) 
    : ((Loc.t list) option) m = 
  let* points = 
    Local.filterM (fun name vb ->
        match vb with 
        | VariableBinding.UsedResource (re, where) -> 
           let* holds = for_fp_filter loc {local; global} (pointer_it, size) name re in
           return (if holds then Some (where) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points







open LogicalConstraints


let rec remove_owned_subtree (loc: Loc.t) {local;global} (bt : BT.t) (pointer: IT.t) (size: size) 
          access_kind is_field = 
  match bt with
  | Struct tag ->
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     ListM.fold_leftM (fun local (member,bt) ->
         remove_owned_subtree loc {local;global} bt
           (IT.MemberOffset (tag,pointer,member)) size access_kind (Some member)
       ) local decl.raw
  | _ ->
     let* o_member_resource = for_fp loc {local;global} (pointer,size) in
     match o_member_resource with
     | Some (rname,_) -> Local.use_resource loc rname [loc] local
     | None -> 
        let* olast_used = for_fp_used loc {local;global} (pointer,size) in
        fail loc (Missing_ownership (access_kind, is_field, olast_used))



  
let rec load (loc: Loc.t) 
             {local;global}
             (bt: BT.t)
             (pointer: IT.t)
             (size: RE.size)
             (path: IT.t)
             (is_field: BT.member option) 
  =
  let open RT in
  match bt with
  | Struct tag ->
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     let rec aux = function
       | (member,member_bt)::members ->
          let member_pointer = IT.MemberOffset (tag,pointer,member) in
          let member_path = IT.Member (tag, path, member) in
          let member_size = List.assoc member decl.sizes in
          let* constraints = aux members in
          let* constraints2 = load loc {local;global} member_bt member_pointer 
                                member_size member_path (Some member)in
          return (constraints2@@constraints)
       | [] -> return I
     in  
     aux decl.raw
  | _ ->
     let* o_resource = for_fp loc {local;global} (pointer,size) in
     let* pointee = match o_resource with
       | Some (_,Points p) -> return p.pointee
       | Some (_,Uninit _) -> fail loc (Uninitialised is_field)
       | None -> 
          let* olast_used = for_fp_used loc {local;global} (pointer,size) in
          fail loc (Missing_ownership (Load, is_field, olast_used))
     in
     let* vls = Local.get_l loc pointee local in
     if LS.equal vls (Base bt) 
     then return (Constraint (LC (IT.EQ (path, S pointee)),I))
     else fail loc (Mismatch {has=vls; expect=Base bt})



(* does not check for the right to write, this is done elsewhere *)
let rec store (loc: Loc.t)
              {local;global}
              (bt: BT.t)
              (pointer: IT.t)
              (size: RE.size)
              (o_value: IT.t option) 
  =
  let open RT in
  match bt with
  | Struct tag ->
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     let rec aux = function
       | [] -> return I
       | (member,member_bt)::members ->
          let member_pointer = IT.MemberOffset (tag,pointer,member) in
          let member_size = List.assoc member decl.sizes in
          let o_member_value = Option.map (fun v -> IT.Member (tag, v, member)) o_value in
          let* rt = aux members in
          let* rt2 = store loc {local;global} member_bt member_pointer 
                              member_size o_member_value in
          return (rt@@rt2)
     in  
     aux decl.raw
  | _ -> 
     let vsym = Sym.fresh () in 
     match o_value with
       | Some v -> 
          let rt = 
            Logical ((vsym, Base bt), 
            Resource (Points {pointer; pointee = vsym; size}, 
            Constraint (LC (EQ (S vsym, v)), I)))
          in
          return rt
       | None -> 
          return (Resource (Uninit {pointer; size}, I))
