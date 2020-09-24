module Loc = Locations
module RE = Resources
module IT = IndexTerms
open Environment
open Resultat
open RE
open TypeErrors
open Pp

let match_resource (loc: Loc.t) {local;global} shape : ((Sym.t * RE.t) option) m = 
  let* found = 
    Local.filter_rM (fun name t -> 
        if match_shape shape t then
          let* equal = Solver.equal loc {local;global} 
                         (shape_pointer shape) (pointer t) in
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
           let* holds = Solver.equal loc {local;global} 
                          loc_it p.pointer in
           return (if holds then Some (name,p) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points



let match_concrete_resource (loc: Loc.t) {local;global} (resource: RE.t) : ((Sym.t * RE.t) option) m = 
  match_resource loc {local;global} (RE.shape resource)



open LogicalConstraints
module RT = ReturnTypes


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
     let shape = Points_ (pointer,size) in
     let* o_member_resource = match_resource loc {local;global} shape in
     match o_member_resource with
     | None -> fail loc (Missing_ownership (access_kind,is_field))
     | Some (rname,r) -> Local.use_resource loc rname [loc] local


let load_point loc {local;global} bt pointer size path is_field = 
  let* o_resource = points_to loc {local;global} pointer size in
  let* pointee = match o_resource with
    | Some (_,{pointee = Some pointee; _}) -> return pointee
    | Some (_,{pointee = None; _}) -> fail loc (Uninitialised is_field)
    | None -> fail loc (Missing_ownership (Load, is_field))
  in
  let* vbt = IndexTermTyping.infer_index_term loc {local;global} pointee in
  if LS.equal vbt (Base bt) then return [LC (IT.EQ (path, pointee))]
  else fail loc (Mismatch {has=vbt; expect=Base bt})
  
let rec load_struct (loc: Loc.t) {local;global} (tag: BT.tag) (pointer: IT.t) (path: IT.t) =
  let open RT in
  let* decl = Global.get_struct_decl loc global.struct_decls tag in
  let rec aux = function
    | (member,member_bt)::members ->
       let member_pointer = IT.MemberOffset (tag,pointer,member) in
       let member_path = IT.Member (tag, path, member) in
       let member_size = List.assoc member decl.sizes in
       let* constraints = aux members in
       let* constraints2 = match member_bt with
         | BT.Struct tag2 -> load_struct loc {local;global} tag2 member_pointer member_path
         | _ -> load_point loc {local;global} member_bt member_pointer member_size member_path (Some member)
       in
       return (constraints2@constraints)
    | [] -> return []
  in  
  aux decl.raw


(* TODO: can be simplified if we allow index terms on the right of points-to *)
let rec store_struct
          (loc: Loc.t)
          (struct_decls: Global.struct_decls) (tag: BT.tag)
          (pointer: IT.t)
          (o_value: IT.t option) 
  =
  (* does not check for the right to write, this is done elsewhere *)
  let open RT in
  let* decl = Global.get_struct_decl loc struct_decls tag in
  let rec aux = function
    | (member,bt)::members ->
       let member_pointer = IT.MemberOffset (tag,pointer,member) in
       let o_member_value = Option.map (fun v -> IT.Member (tag, v, member)) o_value in
       let* (lbindings,rbindings) = aux members in
       let* (lbindings',rbindings') = match bt with
         | BT.Struct tag2 -> 
            let* (lbindings2,rbindings2) = 
              store_struct loc struct_decls tag2 member_pointer o_member_value in
            return (lbindings2@@lbindings, rbindings2@@rbindings)
         | _ -> 
            let size = List.assoc member decl.sizes in
            let points = {pointer = member_pointer; pointee = o_member_value; size} in
            return (I,Resource (Points points, I))
       in
       return (lbindings', rbindings')
    | [] -> return (I,I)
  in  
  aux decl.raw


