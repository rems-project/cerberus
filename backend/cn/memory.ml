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



let size_of_ctype (ct : Sctypes.t) = 
  match ct with
  | Sctypes.Sctype (_, Void) -> 
     Debug_ocaml.error "size_of_ctype applied to void"
  | _ -> 
    let s = CF.Impl_mem.sizeof_ival (Sctypes.to_ctype ct) in
    integer_value_to_num s

let align_of_ctype (ct : Sctypes.t) = 
  match ct with
  | Sctypes.Sctype (_, Void) -> 
     Debug_ocaml.error "align_of_ctype applied to void"
  | _ -> 
     let s = CF.Impl_mem.alignof_ival (Sctypes.to_ctype ct) in
     integer_value_to_num s

(* this assumes that we've earlier checked that these only refer to
   already-defined other types (structs, in particular) *)
let rec representable_ctype struct_decls (Sctype (_, ct) : Sctypes.t) about =
  let open Sctypes in
  match ct with
  | Void -> 
     bool_ true
  | Integer it -> 
     IT.in_range about (z_ (min_integer_type it), z_ (max_integer_type it))
  | Array (it, None) -> 
     Debug_ocaml.error "todo: 'representable' for arrays with unknown length"
  | Array (ct, Some n) -> 
     let lcs = 
       List.init n (fun i ->
           representable_ctype struct_decls ct
             (arrayGet_ ~item_bt:(BT.of_sct ct) (about, int_ i))
         )
     in
     and_ lcs
  | Pointer _ -> 
     let pointer_byte_size = size_of_pointer in
     let pointer_size = Z.mult_big_int pointer_byte_size (Z.of_int 8) in
     let max = Z.power_int_positive_big_int 2 pointer_size in
     IT.and_ [IT.lePointer_ (pointer_ Z.zero, about); 
              IT.ltPointer_ (about, pointer_ max)]
  | Struct tag -> 
     let decl = SymMap.find tag struct_decls in
     and_ begin
         List.filter_map (fun Global.{member = (member, sct); _} ->
             let rangef = representable_ctype struct_decls sct in
             let bt = BT.of_sct sct in
             let member_it = 
               IT.structMember_ ~member_bt:bt (tag, about, member) in
             Some (rangef member_it)
           ) (Global.members decl.Global.layout)
       end
  | Function _ -> 
     Debug_ocaml.error "todo: function types"

let size_of_struct tag =
  size_of_ctype (Sctype ([], Struct tag))

let align_of_struct tag =
  align_of_ctype (Sctype ([], Struct tag))


let member_offset struct_decls tag member = 
  let open Global in
  let decl = SymMap.find tag struct_decls in
  let members = Global.members decl.Global.layout in
  (List.find (fun piece -> Id.equal (fst piece.member) member) members).offset



