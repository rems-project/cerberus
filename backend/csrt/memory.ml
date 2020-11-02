module CF = Cerb_frontend
open TypeErrors
open Resultat
open Pp

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms


let integer_value_to_num loc iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc (Internal !^"integer_value_to_num")

let size_of_ctype loc ct = 
  let s = CF.Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let size_of_struct_type loc (BT.Tag s) =
  size_of_ctype loc (CF.Ctype.Ctype ([], CF.Ctype.Struct s))
  
let integer_range loc it =
  let* min = integer_value_to_num loc (CF.Impl_mem.min_ival it) in
  let* max = integer_value_to_num loc (CF.Impl_mem.max_ival it) in
  return (min,max)


open Environment


let for_fp (loc: Loc.t) {local;global} (pointer_it, size) 
    : ((Sym.t * RE.t) option) m = 
  let* points = 
    Local.filter_rM (fun name t ->
        if Z.equal (RE.size t) size then 
          let* holds = Solver.equal loc {local;global} pointer_it (RE.pointer t) in
          if holds then return (Some (name,t)) else return None
        else 
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
     | None -> fail loc (Missing_ownership (access_kind,is_field))
     | Some (rname,_) -> Local.use_resource loc rname [loc] local



  
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
       | None -> fail loc (Missing_ownership (Load, is_field))
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
