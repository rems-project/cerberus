module CF = Cerb_frontend
module BT = BaseTypes


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



let size_of_struct tag =
  size_of_ctype (Sctype ([], Struct tag))

let align_of_struct tag =
  align_of_ctype (Sctype ([], Struct tag))


type struct_piece = 
  { offset: Z.t;
    size: Z.t;
    member_or_padding: (BT.member * Sctypes.t) option }

type struct_layout = struct_piece list

type struct_member = 
  { offset: Z.t;
    size: Z.t;
    member: BT.member * Sctypes.t }


let members = 
  List.filter_map (fun {member_or_padding; offset; size} ->
      Option.bind member_or_padding (fun (member, sctype) ->
          Some {offset; size; member = (member, sctype)}
        )
    )

let member_types =
  List.filter_map (fun {member_or_padding; _} ->
      Option.bind member_or_padding (fun (member, sctype) ->
          Some (member, sctype)
        )
    )




let member_offset (layout : struct_layout) member = 
  let members = members layout in
  (List.find (fun piece -> Id.equal (fst piece.member) member) members).offset



