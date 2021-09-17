module CF = Cerb_frontend
module BT = BaseTypes
module SymMap = Map.Make(Sym)


let report fn exn = 
  Debug_ocaml.error (fn ^ " error: " ^ (Printexc.to_string exn)) 



let integer_value_to_num iv = 
  try
    match CF.Impl_mem.eval_integer_value iv with
    | Some v -> v
    | None -> Debug_ocaml.error "integer_value_to_num returned None"
  with
  | exn -> report "integer_value_to_num" exn



(* adapting from impl_mem *)
let size_of_integer_type it = 
  try
    let impl = CF.Ocaml_implementation.get () in
    match impl.sizeof_ity it with
    | Some n -> n
    | None -> Debug_ocaml.error "sizeof_pointer returned None"
  with
  | exn -> report "size_of_integer_type" exn




(* adapting from impl_mem *)
let align_of_integer_type it =
  try
    let impl = CF.Ocaml_implementation.get () in
    match impl.alignof_ity it with
    | Some n -> n
    | None -> Debug_ocaml.error "alignof_pointer returned None"
  with
  | exn -> report "align_of_integer_type" exn


let max_integer_type it = 
  try
    integer_value_to_num (CF.Impl_mem.max_ival it) 
  with
  | exn -> report "max_integer_type" exn

let min_integer_type it = 
  try
    integer_value_to_num (CF.Impl_mem.min_ival it)
  with
  | exn -> report "min_integer_type" exn



(* adapting from impl_mem *)
let size_of_pointer =
  try 
    let impl = CF.Ocaml_implementation.get () in
    match impl.sizeof_pointer with
    | Some n -> n
    | None -> Debug_ocaml.error "sizeof_pointer returned None"
  with
  | exn -> report "size_of_pointer" exn

(* from impl_mem *)
let align_of_pointer =
  try
    let impl = CF.Ocaml_implementation.get () in
    match impl.alignof_pointer with
    | Some n -> n
    | None -> Debug_ocaml.error "alignof_pointer returned None"
  with
  | exn -> report "align_of_pointer" exn



let size_of_ctype (ct : Sctypes.t) = 
  match ct with
  | Sctypes.Sctype (_, Void) -> 
     Debug_ocaml.error "size_of_ctype applied to void"
  | _ -> 
     try
       let s = CF.Impl_mem.sizeof_ival (Sctypes.to_ctype ct) in
       Z.to_int (integer_value_to_num s)
     with
     | exn -> report "size_of_ctype" exn

let size_of_ctype_opt ct = 
  try Some (size_of_ctype ct) with
  | _ -> None

let align_of_ctype (ct : Sctypes.t) = 
  let open Pp in
  match ct with
  | Sctypes.Sctype (_, Void) -> 
     Debug_ocaml.error "align_of_ctype applied to void"
  (* check this. This is for early alloc *)
  | Sctypes.Sctype (_, Function _) -> 
     1
  | _ -> 
     try
       let s = CF.Impl_mem.alignof_ival (Sctypes.to_ctype ct) in
       Z.to_int (integer_value_to_num s)
     with
     | exn -> report "align_of_ctype" exn



let size_of_struct tag =
  size_of_ctype (Sctype ([], Struct tag))

let align_of_struct tag =
  align_of_ctype (Sctype ([], Struct tag))


type struct_piece = 
  { offset: int;
    size: int;
    member_or_padding: (BT.member * Sctypes.t) option }

type struct_layout = struct_piece list

type struct_member = 
  { offset: int;
    size: int;
    member: BT.member * Sctypes.t }


type struct_decls = struct_layout SymMap.t




let members =
  List.filter_map (fun {member_or_padding; _} ->
      Option.map fst member_or_padding
    )


let member_types =
  List.filter_map (fun {member_or_padding; _} ->
      member_or_padding
    )

let member_number layout member =
  let rec aux i layout = 
    match layout with
    | [] -> None
    | sp :: layout ->
       begin match sp.member_or_padding with
       | Some (member', _) when Id.equal member member' -> Some i
       | Some (_, _) -> aux (i + 1) layout
       | None -> aux i layout
       end 
  in
  aux 0 layout 





let member_offset (layout : struct_layout) member = 
  List.find_map (fun sp -> 
      match sp.member_or_padding with
      | Some (member', _) when Id.equal member member' -> Some sp.offset
      | _ -> None
    ) layout


