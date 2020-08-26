module CF = Cerb_frontend
open TypeErrors
open Except
open Pp

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms


let integer_value_to_num loc iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc (unreachable !^"integer_value_to_num")

let size_of_ctype loc ct = 
  let s = CF.Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let size_of_struct_type loc (BT.Tag s) =
  size_of_ctype loc (CF.Ctype.Ctype ([], CF.Ctype.Struct s))
  
let integer_value_min loc it = 
  integer_value_to_num loc (CF.Impl_mem.min_ival it)

let integer_value_max loc it = 
  integer_value_to_num loc (CF.Impl_mem.max_ival it)

let integer_range loc it =
  let* min = integer_value_min loc it in
  let* max = integer_value_max loc it in
  return (min,max)







let rec store_struct (loc: Loc.t) (struct_decls: Global.struct_decls) (tag: BT.tag) (pointer: IT.t) (o_value: IT.t option) =
  let open IT in
   
  (* does not check for the right to write, this is done elsewhere *)
  let open RT in
  let* decl = Global.get_struct_decl loc struct_decls tag in
  let rec aux = function
    | (member,bt)::members ->
       let member_pointer = Sym.fresh () in
       let pointer_constraint = 
         LC.LC (IT.S member_pointer %= IT.MemberOffset (tag,pointer,member)) in
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
            let* size = size_of_ctype loc (List.assoc member decl.ctypes) in
            let points = {pointer = S member_pointer; pointee = o_member_value; size} in
            return (Logical ((member_pointer, Base Loc), Constraint (pointer_constraint, I)),
                    Resource (Points points, I))
       in
       return ((member,IT.S member_pointer)::mapping, lbindings', rbindings')
    | [] -> return ([],I,I)
  in  
  let* (members,lbindings,rbindings) = aux decl.raw in
  let* size = size_of_struct_type loc tag in
  let stored = {pointer; tag; size; members} in
  return (stored, lbindings, rbindings)


