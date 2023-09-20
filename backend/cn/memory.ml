module CF = Cerb_frontend
module BT = BaseTypes
module SymMap = Map.Make(Sym)
module IM = struct include CF.Impl_mem include CF.Mem end
module OI = CF.Ocaml_implementation
open Sctypes

(* ... adapting from impl_mem *)


let bits_per_byte = 8

let z_of_ival iv = Option.get (IM.eval_integer_value iv)
let int_of_ival iv = Z.to_int (Option.get (IM.eval_integer_value iv))


let size_of_integer_type it = Option.get ((OI.get ()).sizeof_ity it)
let align_of_integer_type it = Option.get ((OI.get ()).alignof_ity it)
let is_signed_integer_type ity = (OI.get ()).is_signed_ity ity

let max_integer_type it = z_of_ival (CF.Impl_mem.max_ival it) 
let min_integer_type it = z_of_ival (CF.Impl_mem.min_ival it)

let size_of_pointer = Option.get ((OI.get ()).sizeof_pointer)
let align_of_pointer = Option.get ((OI.get ()).alignof_pointer)

let max_pointer = 
  let pointer_bits = size_of_pointer * bits_per_byte in
  Z.sub (Z.pow (Z.of_int 2) pointer_bits) (Z.of_int 1)

let bt_of_sct = BT.of_sct is_signed_integer_type size_of_integer_type
let sbt_of_sct = SurfaceBaseTypes.of_sct is_signed_integer_type size_of_integer_type

let intptr_bt = bt_of_sct Sctypes.(Integer (Unsigned Intptr_t))

let size_of_ctype = function
  | Void -> Cerb_debug.error "size_of_ctype applied to void"
  | ct -> int_of_ival (IM.sizeof_ival (to_ctype ct))

let align_of_ctype = function
  | Void -> 1
  | Function _ -> 1
  | ct -> int_of_ival (IM.alignof_ival (Sctypes.to_ctype ct))


type struct_piece = { 
    offset: int;
    size: int;
    member_or_padding: (Id.t * Sctypes.t) option 
  }

type struct_member = { 
    offset: int;
    size: int;
    member: Id.t * Sctypes.t 
  }

type struct_layout = struct_piece list
type struct_decl = struct_layout
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





let member_offset (layout : struct_layout) member : int option = 
  List.find_map (fun sp -> 
      match sp.member_or_padding with
      | Some (member', _) when Id.equal member member' -> Some sp.offset
      | _ -> None
    ) layout




