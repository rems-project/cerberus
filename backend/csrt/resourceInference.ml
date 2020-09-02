module Loc = Locations
module RE = Resources
open Environment
open Result
open RE
open TypeErrors
open Pp

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

