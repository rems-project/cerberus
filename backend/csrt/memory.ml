module CF = Cerb_frontend
open IndexTerms

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms


let integer_value_to_num iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> v
  | None -> Debug_ocaml.error "integer_value_to_num returned None"



(* adapting from impl_mem *)
let size_of_integer_type it = 
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_ity it with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "sizeof_pointer returned None"

(* adapting from impl_mem *)
let align_of_integer_type it =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_ity it with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "alignof_pointer returned None"

let max_integer_type it = 
  integer_value_to_num (CF.Impl_mem.max_ival it) 

let min_integer_type it = 
  integer_value_to_num (CF.Impl_mem.min_ival it)

let representable_integer_type it about =
  let (min,max) = match it with
    | CF.Ctype.Bool -> (Z.of_int 0, Z.of_int 1)
    | _ -> (min_integer_type it, max_integer_type it)
  in
  LC.LC (IT.in_range about (Num min, Num max))




(* adapting from impl_mem *)
let size_of_pointer =
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_pointer with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "sizeof_pointer returned None"

(* from impl_mem *)
let align_of_pointer =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_pointer with
  | Some n -> Z.of_int n
  | None -> Debug_ocaml.error "alignof_pointer returned None"


let representable_pointer about = 
  let pointer_byte_size = size_of_pointer in
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


let size_of_ctype (ct : Sctypes.t) = 
  let s = CF.Impl_mem.sizeof_ival (Sctypes.to_ctype ct) in
  integer_value_to_num s

let align_of_ctype (ct : Sctypes.t) = 
  let s = CF.Impl_mem.alignof_ival (Sctypes.to_ctype ct) in
  integer_value_to_num s

(* this assumes that we've earlier checked that these only refer to
   already-defined other types (structs, in particular) *)
let rec representable_ctype struct_decls (Sctype (_, ct) : Sctypes.t) about =
  let open Sctypes in
  match ct with
  | Void -> LC.LC (Bool true)
  | Integer it -> representable_integer_type it about
  | Pointer _ -> representable_pointer about
  | Struct tag -> representable_struct struct_decls tag about

and representable_struct struct_decls tag about =
  let decl = SymMap.find tag struct_decls in
  let lcs =
    List.filter_map (fun Global.{member = (member, sct); _} ->
            let rangef = representable_ctype struct_decls sct in
            Some (LC.unpack (rangef (IT.StructMember (tag, about, member))))
      ) (Global.members decl.Global.layout)
  in
  (LC.LC (And lcs))


let size_of_struct tag =
  size_of_ctype (Sctype ([], Struct tag))

let align_of_struct tag =
  align_of_ctype (Sctype ([], Struct tag))


let member_offset tag member = 
  let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) tag member in
  integer_value_to_num iv







let size_of_stored_type st = 
  match st with
  | ST.ST_Ctype ct -> size_of_ctype ct
  | ST.ST_Pointer -> size_of_pointer

let align_of_stored_type st = 
  match st with
  | ST.ST_Ctype ct -> align_of_ctype ct
  | ST.ST_Pointer -> align_of_pointer

let representable_stored_type struct_decls st = 
  match st with
  | ST.ST_Ctype ct -> representable_ctype struct_decls ct
  | ST.ST_Pointer -> representable_pointer
