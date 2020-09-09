module Loc = Locations
module RE = Resources
module IT = IndexTerms
open Environment
open Resultat
open RE
open TypeErrors
open Pp
open List

let match_resource (loc: Loc.t) {local;global} shape : ((Sym.t * RE.t) option) m = 
  let* found = 
    Local.filter_rM (fun name t -> 
        if match_shape shape t then
          let* equal = Solver.equal loc {local;global} (shape_pointer shape) (pointer t) in
          return (if equal then Some (name,t) else None)
        else 
          return None
      ) local
  in
  match found with
  | [] -> return None
  | [r] -> return (Some r)
  | _ -> fail loc (unreachable (!^"multiple matching resources:" ^^^ pp_list (fun (_,r) -> RE.pp false r) found))


let points_to (loc: Loc.t) {local;global} (loc_it: IT.t) (size: size) 
    : ((Sym.t * RE.points) option) m = 
  let* points = 
    Local.filter_rM (fun name t ->
        match t with
        | RE.Points p when Num.equal p.size size ->
           let* holds = Solver.equal loc {local;global} loc_it p.pointer in
           return (if holds then Some (name,p) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points


let stored_struct_to (loc: Loc.t) {local;global} (loc_it: IT.t) (tag: BT.tag) : ((Sym.t * RE.stored_struct) option) m = 
  let* stored = 
    Local.filter_rM (fun name t ->
        match t with
        | RE.StoredStruct s when s.tag = tag ->
           let* holds = Solver.equal loc {local;global} loc_it s.pointer in
           return (if holds then Some (name,s) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" stored



let match_concrete_resource (loc: Loc.t) {local;global} (resource: RE.t) : ((Sym.t * RE.t) option) m = 
  match_resource loc {local;global} (RE.shape resource)



let rec remove_owned_subtree (loc: Loc.t) {local;global} ((re_name:Sym.t), (re:RE.t)) = 
  match re with
  | StoredStruct s ->
     let* decl = Global.get_struct_decl loc global.struct_decls s.tag in
     ListM.fold_leftM (fun local (member,member_pointer) ->
         let bt = List.assoc member decl.raw  in
         let ct = List.assoc member decl.ctypes  in
         let* size = Memory.size_of_ctype loc ct in
         let* local = Local.use_resource loc re_name [loc] local in
         let shape = match bt with
           | Struct tag -> StoredStruct_ (member_pointer, tag)
           | _ -> Points_ (member_pointer,size)
         in
         let* o_member_resource = match_resource loc {local;global} shape in
         match o_member_resource with
         | Some (rname,r) -> remove_owned_subtree loc {local;global} (rname,r)
         | None -> fail loc (Generic !^"missing ownership for de-allocating")
       ) local s.members
  | Points _ ->
     Local.use_resource loc re_name [loc] local





open LogicalConstraints
module RT = ReturnTypes

let load_point loc {local;global} pointer size bt path is_field = 
  let* o_resource = points_to loc {local;global} pointer size in
  let* pointee = match o_resource, is_field with
    | None, false -> fail loc (Generic !^"missing ownership of load location")
    | None, true -> fail loc (Generic !^"missing ownership of struct field")
    | Some (_,{pointee = None; _}), false -> fail loc (Generic !^"load location uninitialised")
    | Some (_,{pointee = None; _}), true -> fail loc (Generic !^"load location uninitialised")
    | Some (_,{pointee = Some pointee; _}),_  -> 
       return pointee
  in
  let* vbt = IndexTermTyping.infer_index_term loc {local;global} pointee in
  let* () = if BT.equal vbt (Base bt) then return () 
            else fail loc (Mismatch {has=vbt; expect=Base bt}) in
  return [LC (IT.EQ (path, pointee))]
  
let rec load_struct (loc: Loc.t) {local;global} (tag: BT.tag) (pointer: IT.t) (path: IT.t) =
  let open RT in
  let* o_resource = stored_struct_to loc {local;global} pointer tag in
  let* decl = Global.get_struct_decl loc global.struct_decls tag in
  let* (_,stored) = match o_resource with
    | None -> fail loc (Generic !^"missing ownership for loading the struct")
    | Some s -> return s
  in
  let rec aux = function
    | (member,member_pointer)::members ->
       let member_bt = assoc member decl.raw in
       let member_path = IT.Member (tag, path, member) in
       let* member_size = Memory.size_of_ctype loc (assoc member decl.ctypes) in
       let* constraints = aux members in
       let* constraints2 = match member_bt with
         | Struct tag2 -> load_struct loc {local;global} tag2 member_pointer member_path
         | _ -> load_point loc {local;global} member_pointer member_size member_bt member_path true
       in
       return (constraints2@constraints)
    | [] -> return []
  in  
  aux stored.members


let rec store_struct (loc: Loc.t) (struct_decls: Global.struct_decls) (tag: BT.tag) (pointer: IT.t) (o_value: IT.t option) =
  let open IT in
   
  (* does not check for the right to write, this is done elsewhere *)
  let open RT in
  let* decl = Global.get_struct_decl loc struct_decls tag in
  let rec aux = function
    | (member,bt)::members ->
       let member_pointer = Sym.fresh () in
       let pointer_constraint = 
         LC.LC (IT.EQ (IT.S member_pointer, IT.MemberOffset (tag,pointer,member))) in
       let o_member_value = Option.map (fun v -> IT.Member (tag, v, member)) o_value in
       let* (mapping,lbindings,rbindings) = aux members in
       let* (lbindings',rbindings') = match bt with
         | BT.Struct tag2 -> 
            let* (stored_struct,lbindings2,rbindings2) = 
              store_struct loc struct_decls tag2 (S member_pointer) o_member_value in
            return (Logical ((member_pointer, Base Loc), 
                      Constraint (pointer_constraint, lbindings2@@lbindings)),
                    Resource (StoredStruct stored_struct, rbindings2@@rbindings))
         | _ -> 
            let* size = Memory.size_of_ctype loc (List.assoc member decl.ctypes) in
            let points = {pointer = S member_pointer; pointee = o_member_value; size} in
            return (Logical ((member_pointer, Base Loc), Constraint (pointer_constraint, I)),
                    Resource (Points points, I))
       in
       return ((member,IT.S member_pointer)::mapping, lbindings', rbindings')
    | [] -> return ([],I,I)
  in  
  let* (members,lbindings,rbindings) = aux decl.raw in
  let* size = Memory.size_of_struct_type loc tag in
  let stored = {pointer; tag; size; members} in
  return (stored, lbindings, rbindings)


