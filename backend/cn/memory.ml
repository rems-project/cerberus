module CF = Cerb_frontend
module BT = BaseTypes
module SymMap = Map.Make(Sym)
module IM = CF.Impl_mem
module OI = CF.Ocaml_implementation
open Sctypes

(* ... adapting from impl_mem *)


let bits_per_byte = 8

let z_of_ival iv = Option.get (IM.eval_integer_value iv)
let int_of_ival iv = Z.to_int (Option.get (IM.eval_integer_value iv))


let size_of_integer_type it = Option.get ((OI.get ()).sizeof_ity it)
let align_of_integer_type it = Option.get ((OI.get ()).alignof_ity it)

let max_integer_type it = z_of_ival (CF.Impl_mem.max_ival it) 
let min_integer_type it = z_of_ival (CF.Impl_mem.min_ival it)

let size_of_pointer = Option.get ((OI.get ()).sizeof_pointer)
let align_of_pointer = Option.get ((OI.get ()).alignof_pointer)


let size_of_ctype = function
  | Sctype (_, Void) -> Debug_ocaml.error "size_of_ctype applied to void"
  | ct -> int_of_ival (IM.sizeof_ival (to_ctype ct))

let align_of_ctype = function
  | Sctype (_, Void) -> 1
  | Sctype (_, Function _) -> 1
  | ct -> int_of_ival (IM.alignof_ival (Sctypes.to_ctype ct))


let size_of_struct tag = size_of_ctype (Sctype ([], Struct tag))
let align_of_struct tag = align_of_ctype (Sctype ([], Struct tag))


type struct_piece = { 
    offset: int;
    size: int;
    member_or_padding: (BT.member * Sctypes.t) option 
  }

type struct_member = { 
    offset: int;
    size: int;
    member: BT.member * Sctypes.t 
  }

type struct_layout = struct_piece list
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







let find_tag struct_decls tag = 
  SymMap.choose
    (SymMap.filter (fun s _ ->
         match Sym.description s with
         | Sym.SD_Id tag' when String.equal tag tag' -> true
         | _ -> false
       ) struct_decls
    )
