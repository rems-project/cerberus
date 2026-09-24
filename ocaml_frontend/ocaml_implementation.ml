open Ctype
open Cerb_symbol

type type_alias_map = {
  intN_t_alias: int -> integerBaseType option;
  int_leastN_t_alias: int -> integerBaseType option;
  int_fastN_t_alias: int -> integerBaseType option;
  intmax_t_alias: integerBaseType;
  intptr_t_alias: integerBaseType;
  wchar_t_alias: integerType;
  wint_t_alias: integerType;
  size_t_alias: integerType;
  ptrdiff_t_alias: integerType;
}

type implementation = {
  name: string;
  details: string;
  sizeof_pointer: int option;
  alignof_pointer: int option;
  max_alignment: int;
  is_signed_ity: integerType -> bool;
  sizeof_ity: integerType -> int option;
  precision_ity: integerType -> int option;
  sizeof_fty: floatingType -> int option;
  alignof_ity: integerType -> int option;
  alignof_fty: floatingType -> int option;
  register_enum: Sym.t -> Z.t list -> bool;
  typeof_enum: Sym.t -> integerType;
  type_alias_map: type_alias_map;
}

module type Implementation = sig
  val impl: implementation
end

module Common = struct
  let normalise_integerType_ type_alias_map typeof_enum ity =
    let aux_ibty = function
      | IntN_t n ->
          Option.get (type_alias_map.intN_t_alias n)
      | Int_leastN_t n ->
          Option.get (type_alias_map.int_leastN_t_alias n)
      | Int_fastN_t n ->
          Option.get (type_alias_map.int_fastN_t_alias n)
      | Intmax_t ->
          type_alias_map.intmax_t_alias
      | Intptr_t ->
          type_alias_map.intptr_t_alias
      | ibty -> ibty in
  match ity with
    | Signed ibty ->
        Signed (aux_ibty ibty)
    | Unsigned ibty ->
        Unsigned (aux_ibty ibty)
    | Enum tag_sym ->
        typeof_enum tag_sym
    | Wchar_t ->
        type_alias_map.wchar_t_alias
    | Wint_t ->
        type_alias_map.wint_t_alias
    | Size_t ->
        type_alias_map.size_t_alias
    | Ptrdiff_t ->
        type_alias_map.ptrdiff_t_alias
    | ity ->
        ity

  let precision_ity ~sizeof_ity ~is_signed_ity ity =
    match sizeof_ity ity with
      | Some n ->
          if is_signed_ity ity then
            Some (8*n-1)
          else
            Some (8*n)
      | None ->
          None
  
  (* NOTE: some of them are not implementation defined *)
  let is_signed_ity ~typeof_enum ~char_is_signed ity =
    let ity' =
      match ity with
        | Enum tag_sym ->
            typeof_enum tag_sym
        | _ ->
            ity in
    match ity' with
      | Char ->
          char_is_signed
      | Bool ->
          false
      | Signed _ ->
          true
      | Unsigned _ ->
          false
      | Enum tag_sym ->
          assert false
      | Size_t ->
          (* STD §7.19#2 *)
          false
      | Wchar_t ->
          true
      | Wint_t ->
          true
      | Ptrdiff_t ->
          (* STD §7.19#2 *)
          true
      | Ptraddr_t ->
          false
end

let normalise_integerType impl =
  Common.normalise_integerType_ impl.type_alias_map impl.typeof_enum

module DefaultImpl = struct
  let name = "clang9_x86_64-apple-darwin16.7.0"
  let details = "Apple LLVM version 9.0.0 (clang-900.0.38)\nTarget: x86_64-apple-darwin16.7.0"

  let sizeof_pointer =
    Some 8

  let alignof_pointer =
    Some 8

  (* INTERNAL *)
  let registered_enums =
    ref []

  (* NOTE: for enums implementation we follow GCC, since Clang doesn't document
     it's implementation details... *)
  let register_enum tag_sym ns =
    (* NOTE: we don't support GCC's -fshort-enums option *)
    let ity =
      if List.exists (fun n -> Z.lt n Z.zero) ns then
        Signed Int_
      else
        Unsigned Int_ in
    if List.exists (fun (z, _) -> Sym.compare z tag_sym = 0) !registered_enums then
      false
    else begin
      registered_enums := (tag_sym, ity) :: !registered_enums;
      true
    end

  let typeof_enum tag_sym =
    match List.find_opt (fun (z, _) -> Sym.compare z tag_sym = 0) !registered_enums with
      | None ->
          failwith ("Ocaml_implementation.typeof_enum: '" ^
                    Sym.show tag_sym ^ "' was not registered")
      | Some (_, z) ->
          z
  let max_alignment =
    8
  
  let type_alias_map =
    let n_t_aliases = function
    | 8  -> Some Ichar
    | 16 -> Some Short
    | 32 -> Some Int_
    | 64 -> Some Long
    | _  -> None in
    {
    intN_t_alias= n_t_aliases;
    int_leastN_t_alias= n_t_aliases;
    int_fastN_t_alias= n_t_aliases;
    intmax_t_alias= Long;
    intptr_t_alias= Long;
    wchar_t_alias= Signed Int_; (*TODO: check *)
    wint_t_alias= Signed Int_;
    size_t_alias= Unsigned Long;
    ptrdiff_t_alias= Signed Long;
  }

  let sizeof_ity ity =
    match Common.normalise_integerType_ type_alias_map typeof_enum ity with
      | Char
      | Bool ->
          Some 1
      | Signed ibty
      | Unsigned ibty ->
          Some begin match ibty with
            | Ichar ->
                1
            | Short ->
                2
            | Int_ ->
                4
            | Long
            | LongLong ->
                8
            | IntN_t _
            | Int_leastN_t _
            | Int_fastN_t _
            | Intmax_t
            | Intptr_t ->
                assert false
          end
      | Enum _
      | Wchar_t
      | Wint_t
      | Size_t
      | Ptrdiff_t ->
          assert false
      | Ptraddr_t ->
          Some 8

  let sizeof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16

  let alignof_ity ity =
    match Common.normalise_integerType_ type_alias_map typeof_enum ity with
      | Char
      | Bool ->
          Some 1
      | Signed ibty
      | Unsigned ibty ->
          Some begin match ibty with
            | Ichar ->
                1
            | Short ->
                2
            | Int_ ->
                4
            | Long
            | LongLong ->
                8
            | IntN_t _
            | Int_leastN_t _
            | Int_fastN_t _
            | Intmax_t
            | Intptr_t ->
                assert false
          end
      | Enum _
      | Wchar_t
      | Wint_t
      | Size_t
      | Ptrdiff_t ->
          assert false
      | Ptraddr_t ->
          Some 8

  let alignof_fty = function
    | RealFloating Float ->
        Some 8 (* TODO:hack ==> 4 *)
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 8 (* TODO:hack ==> 16 *)
  
  (* CAUTION!! new implementions based on DefaultImpl should redefine this *)
  let impl: implementation =
    let is_signed_ity = Common.is_signed_ity ~typeof_enum ~char_is_signed:true in
    {
      name;
      details;
      sizeof_pointer;
      alignof_pointer;
      max_alignment;
      is_signed_ity;
      sizeof_ity;
      precision_ity= Common.precision_ity ~sizeof_ity ~is_signed_ity;
      sizeof_fty;
      alignof_ity;
      alignof_fty;
      register_enum;
      typeof_enum;
      type_alias_map;
    }
end


(* module DefactoImpl = struct
  include DefaultImpl

  (* TODO:
    The observable, integer range of a uintptr_t is the same as that
    of a ptraddr_t (or ptrdiff_t for intptr_t ), despite the increased
    alignment and storage requirements.
   *)

  let sizeof_ity = function
    | Signed Intptr_t  | Unsigned Intptr_t -> Some 16
    | ity ->  DefaultImpl.sizeof_ity ity

  let alignof_ity = function
    | Signed Intptr_t  | Unsigned Intptr_t -> Some 16
    | ity ->  DefaultImpl.alignof_ity ity
  
  let impl = { DefaultImpl.impl with
    sizeof_ity;
    alignof_ity;
  }
end *)

module MorelloImpl = struct
  let name = "clang11_aarch64-unknown-freebsd13"
  let details = "clang version 11.0.0\nTarget: Morello"

  let sizeof_pointer =
    Some 16

  let alignof_pointer =
    Some 16

  let max_alignment =
    16
  
  let type_alias_map = { DefaultImpl.type_alias_map with
    intptr_t_alias= LongLong;
  }

  let register_enum = DefaultImpl.register_enum
  let typeof_enum = DefaultImpl.typeof_enum
  
  let alignof_ity ity =
    match Common.normalise_integerType_ type_alias_map typeof_enum ity with
      | Signed LongLong
      | Unsigned LongLong -> Some 16
      | ity ->  DefaultImpl.alignof_ity ity

  let sizeof_ity ity =
    match Common.normalise_integerType_ type_alias_map typeof_enum ity with
      | Signed LongLong
      | Unsigned LongLong -> Some 16
      | ity ->  DefaultImpl.sizeof_ity ity
  
  let sizeof_fty = DefaultImpl.sizeof_fty
  let alignof_fty = DefaultImpl.alignof_fty

  let impl: implementation =
    let is_signed_ity = Common.is_signed_ity ~typeof_enum ~char_is_signed:true in
    {
      name;
      details;
      sizeof_pointer;
      alignof_pointer;
      max_alignment;
      is_signed_ity;
      sizeof_ity;
      precision_ity= Common.precision_ity ~sizeof_ity ~is_signed_ity;
      sizeof_fty;
      alignof_ity;
      alignof_fty;
      register_enum;
      typeof_enum;
      type_alias_map;
    }
end


(* LP64 *)
module HafniumImpl = struct
  let name = "hafnium_aarch64-none-eabi"
  let details = "TODO"

  (* let sizeof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16 *)

  (* let alignof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16 *)
  
  let impl: implementation =
    let is_signed_ity = Common.is_signed_ity ~typeof_enum:DefaultImpl.typeof_enum ~char_is_signed:false in
    let sizeof_ity= DefaultImpl.sizeof_ity in
    {
      name;
      details;
      sizeof_pointer= DefaultImpl.sizeof_pointer;
      alignof_pointer= DefaultImpl.alignof_pointer;
      max_alignment= DefaultImpl.max_alignment;
      is_signed_ity;
      sizeof_ity;
      precision_ity= Common.precision_ity ~sizeof_ity ~is_signed_ity;
      sizeof_fty= DefaultImpl.sizeof_fty;
      alignof_ity= DefaultImpl.alignof_ity;
      alignof_fty= DefaultImpl.alignof_fty;
      register_enum= DefaultImpl.register_enum;
      typeof_enum= DefaultImpl.typeof_enum;
      type_alias_map= DefaultImpl.type_alias_map;
    }
end


let hafniumIntImpl: IntegerImpl.implementation =
  let open IntegerImpl in
  make_implementation Two'sComplement 
  HafniumImpl.impl.is_signed_ity
  (fun ity ->
    match HafniumImpl.impl.precision_ity ity with
      | Some n -> n
      | None   -> assert false)
  (Size_t)
  (Ptrdiff_t)
  (Ptraddr_t)


(* TODO: this is horrible... *)
let (set, get) : (implementation -> unit) * (unit -> implementation) =
  (* NOTE: to prevent nasty bugs the setter can only be called once *)
  let selected =
    ref (false, DefaultImpl.impl) in
  ( begin fun new_impl ->
      if fst !selected then
        failwith "Ocaml_implementation: attempted a second set() of the implementation"
      else
        selected := (true, new_impl)
    end
  , begin fun () ->
      snd !selected
    end )


module Z = struct
  include Z
  let modulus = erem
end

exception Missing_implementation_detail of string

(* TODO: memoise this, it's stupid to recompute this every time... *)
(* NOTE: returns ([(memb_ident, type, offset)], last_offset) *)
let rec offsetsof ?(ignore_flexible=false) tagDefs tag_sym =
  let open Z in
  match Pmap.find tag_sym tagDefs with
  | _, StructDef (membrs_, flexible_opt) ->
      (* NOTE: the offset of a flexible array member is just like
          that of any other member *)
      let membrs = match flexible_opt with
      | None -> membrs_
      | Some (FlexibleArrayMember (attrs, ident, qs, ty)) ->
          if ignore_flexible then
            membrs_
          else
            membrs_ @ [(ident, (attrs, None, qs, ty))] in
      let (xs, maxoffset) =
        List.fold_left (fun (xs, last_offset) (membr, (_, align_opt, _, ty)) ->
          let size = sizeof tagDefs ty in
          let align =
            match align_opt with
            | None -> alignof tagDefs ty
            | Some (AlignInteger al_n) -> al_n
            | Some (AlignType al_ty) -> alignof tagDefs al_ty in
          let x = modulus last_offset align in
          let pad = if equal x zero then zero else sub align x in
          ((membr, ty, add last_offset pad) :: xs, add (add last_offset pad) size)
        ) ([], zero) membrs in
      (List.rev xs, maxoffset)
  | _, UnionDef membrs ->
      (List.map (fun (ident, (_, _, _, ty)) -> (ident, ty, zero)) membrs, zero)


and sizeof tagDefs (Ctype (_, ty) as cty) : Z.t =
  let open Z in
  match ty with
  | Void | Array (_, None) | Function _ | FunctionNoParams _ ->
      assert false
  | Basic (Integer ity) ->
      begin match (get ()).sizeof_ity ity with
      | Some n -> of_int n
      | None -> raise @@ Missing_implementation_detail "sizeof an ITY"
      end
  | Basic (Floating fty) ->
      begin match (get ()).sizeof_fty fty with
      | Some n -> of_int n
      | None -> raise @@ Missing_implementation_detail "sizeof a FLOAT"
      end
  | Array (elem_ty, Some n) ->
      mul n (sizeof tagDefs elem_ty)
  | Pointer _ ->
      begin match (get ()).sizeof_pointer with
      | Some n -> of_int n
      | None -> raise @@ Missing_implementation_detail "sizeof a POINTER"
      end
  | Atomic atom_ty ->
      sizeof tagDefs atom_ty
  | Struct tag_sym ->
      (* NOTE: the potential flexible array member indirectly take part in the size
          by potentially introducing trailling padding bytes if its presence increases
          the alignment requirement. This is done by the call the to alignof here.
          But other than for these padding bytes, it is not counted in the size
          (hence the `ignore_flexible` in the call to offsetof) *)
      let (_, max_offset) = offsetsof ~ignore_flexible:true tagDefs tag_sym in
      let align = alignof tagDefs cty in
      let x = modulus max_offset align in
      if equal x zero then max_offset else Z.add max_offset (Z.sub align x)
  | Union tag_sym ->
      begin match Pmap.find tag_sym tagDefs with
      | _, StructDef _ -> assert false
      | _, UnionDef membrs ->
          let (max_size, max_align) =
            List.fold_left (fun (acc_size, acc_align) (_, (_, align_opt, _, ty)) ->
              let align =
                match align_opt with
                | None -> alignof tagDefs ty
                | Some (AlignInteger al_n) -> al_n
                | Some (AlignType al_ty) -> alignof tagDefs al_ty in
              (max acc_size (sizeof tagDefs ty), max acc_align align)
            ) (zero, zero) membrs in
          (* NOTE: adding padding at the end to satisfy the alignment constraints *)
          let x = modulus max_size max_align in
          if equal x zero then max_size else add max_size (sub max_align x)
      end
  | Byte ->
      of_int 1

and alignof tagDefs (Ctype (_, ty)) : Z.t =
  match ty with
  | Void -> assert false
  | Basic (Integer ity) ->
      begin match (get ()).alignof_ity ity with
      | Some n -> Z.of_int n
      | None -> raise @@ Missing_implementation_detail "alignof an INTEGER"
      end
  | Basic (Floating fty) ->
      begin match (get ()).alignof_fty fty with
      | Some n -> Z.of_int n
      | None -> raise @@ Missing_implementation_detail "alignof a FLOATING"
      end
  | Array (elem_ty, _) -> alignof tagDefs elem_ty
  | Function _
  | FunctionNoParams _ -> assert false
  | Pointer _ ->
      begin match (get ()).alignof_pointer with
      | Some n -> Z.of_int n
      | None -> raise @@ Missing_implementation_detail "alignof a POINTER"
      end
  | Atomic atom_ty ->
      alignof tagDefs atom_ty
  | Struct tag_sym ->
      begin match Pmap.find tag_sym tagDefs with
      | _, UnionDef _ -> assert false
      | _, StructDef (membrs, flexible_opt)  ->
          (* NOTE: we take into account the potential flexible array member by tweaking
              the accumulator init of the fold. *)
          let init = match flexible_opt with
            | None -> Z.zero
            | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
                alignof tagDefs (Ctype ([], Array (elem_ty, None))) in
          (* NOTE: Structs (and unions) alignment is that of the maximum alignment
              of any of their components. *)
          List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
            let memb_align =
              match align_opt with
              | None -> alignof tagDefs ty
              | Some (AlignInteger al_n) -> al_n
              | Some (AlignType al_ty) -> alignof tagDefs al_ty in
            max memb_align acc
          ) init membrs
      end
  | Union tag_sym ->
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
      | _, StructDef _ -> assert false
      | _, UnionDef membrs ->
          (* NOTE: Structs (and unions) alignment is that of the maximum alignment
              of any of their components. *)
          List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
            let memb_align =
              match align_opt with
              | None ->
                  alignof tagDefs ty
              | Some (AlignInteger al_n) ->
                  al_n
              | Some (AlignType al_ty) ->
                alignof tagDefs al_ty in
            max memb_align acc
          ) Z.zero membrs
      end
  | Byte ->
      Z.one
