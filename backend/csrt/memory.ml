module CF = Cerb_frontend
open IndexTerms

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms


let integer_value_to_num loc iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> v
  | None -> Debug_ocaml.error "integer_value_to_num returned None"



(* adapting from impl_mem *)
let size_of_integer_type loc it = 
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_ity it with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "sizeof_pointer returned None"

(* adapting from impl_mem *)
let align_of_integer_type loc it =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_ity it with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "alignof_pointer returned None"

let representable_integer_type loc it about =
  let (min,max) = match it with
    | CF.Ctype.Bool -> 
       (Z.of_int 0, Z.of_int 1)
    | _ -> 
       let min = integer_value_to_num loc (CF.Impl_mem.min_ival it) in
       let max = integer_value_to_num loc (CF.Impl_mem.max_ival it) in
       (min, max)
  in
  LC.LC (IT.in_range (Num min) (Num max) about)




(* adapting from impl_mem *)
let size_of_pointer loc =
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_pointer with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "sizeof_pointer returned None"

(* from impl_mem *)
let align_of_pointer loc =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_pointer with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "alignof_pointer returned None"


let representable_pointer loc about = 
  let pointer_byte_size = size_of_pointer loc in
  let pointer_size = Z.mult_big_int pointer_byte_size (Z.of_int 8) in
  let max = Z.power_int_positive_big_int 2 (Z.sub_big_int pointer_size (Z.of_int 1)) in
  LC.LC (IT.And [IT.LocLE (Pointer Z.zero, about); 
                 IT.LocLE (about, Pointer max)])
  





(* let lookup_struct_in_tagDefs loc tag =
 *   match Pmap.lookup tag (CF.Tags.tagDefs ()) with
 *   | Some (CF.Ctype.StructDef (fields,flexible_array_member)) -> 
 *      (fields,flexible_array_member)
 *   | Some (UnionDef _) -> Debug_ocaml.error "lookup_struct_in_tagDefs: union"
 *   | None -> 
 *      Debug_ocaml.error "lookup_struct_in_tagDefs: struct not found" *)


let size_of_ctype loc (ct : Sctypes.t) = 
  let s = CF.Impl_mem.sizeof_ival (Sctypes.to_ctype ct) in
  integer_value_to_num loc s

let align_of_ctype loc (ct : Sctypes.t) = 
  let s = CF.Impl_mem.alignof_ival (Sctypes.to_ctype ct) in
  integer_value_to_num loc s

(* this assumes that we've earlier checked that these only refer to
   already-defined other types (structs, in particular) *)
let rec representable_ctype loc struct_decls (ct : Sctypes.t) about =
  let open Sctypes in
  match ct with
  | Void -> LC.LC (Bool true)
  | Integer it -> representable_integer_type loc it about
  | Pointer _ -> representable_pointer loc about
  | Struct tag -> representable_struct loc struct_decls tag about

and representable_struct loc struct_decls tag about =
  let decl = SymMap.find tag struct_decls in
  let lcs =
    List.map (fun (member, (ct, _)) ->
        let rangef = representable_ctype loc struct_decls ct in
        LC.unpack (rangef (IT.Member (tag, about, member)))
      ) decl.Global.members
  in
  (LC.LC (And lcs))


let size_of_struct loc tag =
  size_of_ctype loc (Struct tag)

let align_of_struct loc tag =
  align_of_ctype loc (Struct tag)


let member_offset loc tag member = 
  let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) tag member in
  integer_value_to_num loc iv







let size_of_stored_type loc st = 
  match st with
  | ST.ST_Ctype ct -> size_of_ctype loc ct
  | ST.ST_Pointer -> size_of_pointer loc

let align_of_stored_type loc st = 
  match st with
  | ST.ST_Ctype ct -> align_of_ctype loc ct
  | ST.ST_Pointer -> align_of_pointer loc

let representable_stored_type loc struct_decls st = 
  match st with
  | ST.ST_Ctype ct -> representable_ctype loc struct_decls ct
  | ST.ST_Pointer -> representable_pointer loc
