open IntegerType
open Ctype

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
  register_enum: Symbol.sym -> Nat_big_num.num list -> bool;
  typeof_enum: Symbol.sym -> integerType;
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
      if List.exists (fun n -> Nat_big_num.less n Nat_big_num.zero) ns then
        Signed Int_
      else
        Unsigned Int_ in
    if List.exists (fun (z, _) -> Symbol.symbol_compare z tag_sym = 0) !registered_enums then
      false
    else begin
      registered_enums := (tag_sym, ity) :: !registered_enums;
      true
    end

  let typeof_enum tag_sym =
    match List.find_opt (fun (z, _) -> Symbol.symbol_compare z tag_sym = 0) !registered_enums with
      | None ->
          failwith ("Ocaml_implementation.typeof_enum: '" ^
                    Symbol.instance_Show_Show_Symbol_sym_dict.show_method tag_sym ^ "' was not registered")
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
        Some 8 (* TODO:hack ==> 4 *)
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 8 (* TODO:hack ==> 16 *)

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


(* this is to make it possible to use `alignof' from Cabs_to_ail
   (where tagDefs is a bit different from the Ctype version) *)
let alignof_tagDefs_aux () =
  Pmap.map (function
    | Ctype.StructDef (xs, flex_opt) ->
      List.map (fun (_, (_, align_opt, _, ty)) -> (align_opt, ty)) xs @
      begin match flex_opt with
        | None ->
            []
        | Some (FlexibleArrayMember (_, _, _, ty)) ->
            [(None, Ctype ([], Array (ty, None)))]
      end
    | Ctype.UnionDef xs ->
        List.map (fun (_, (_, align_opt, _, ty)) -> (align_opt, ty)) xs
  ) (Tags.tagDefs ())

let rec alignof ?(tagDefs= alignof_tagDefs_aux ()) (Ctype (_, ty)) =
  match ty with
    | Void ->
        assert false
    | Basic (Integer ity) ->
        begin match (get ()).alignof_ity ity with
          | Some n ->
              Some n
          | None ->
              None
        end
    | Basic (Floating fty) ->
        begin match (get ()).alignof_fty fty with
          | Some n ->
              Some n
          | None ->
              None
        end
    | Array (elem_ty, _) ->
        alignof ~tagDefs elem_ty
    | Function _
    | FunctionNoParams _ ->
        assert false
    | Pointer _ ->
        begin match (get ()).alignof_pointer with
          | Some n ->
              Some n
          | None ->
              None
        end
    | Atomic atom_ty ->
        alignof ~tagDefs atom_ty
    | Struct tag_sym ->
        List.fold_left (fun acc_opt (align_opt, ty) ->
          let al_opt =
            match align_opt with
              | None ->
                  alignof ~tagDefs ty
              | Some (AlignInteger al_n) ->
                  Some (Z.to_int al_n)
              | Some (AlignType al_ty) ->
                  alignof ~tagDefs al_ty in
          match acc_opt, al_opt with
            | Some acc, Some al ->
                Some (max al acc)
            | _ ->
                None
        ) (Some 1) (Pmap.find tag_sym tagDefs)
    | Union tag_sym ->
        (* NOTE: Structs (and unions) alignment is that of the maximum alignment
            of any of their components. *)
        List.fold_left (fun acc_opt (align_opt, ty) ->
          let al_opt =
            match align_opt with
              | None ->
                  alignof ~tagDefs ty
              | Some (AlignInteger al_n) ->
                  Some (Z.to_int al_n)
              | Some (AlignType al_ty) ->
                  alignof ~tagDefs al_ty in
          match acc_opt, al_opt with
            | Some acc, Some al ->
                Some (max al acc)
            | _ ->
                None
        ) (Some 1) (Pmap.find tag_sym tagDefs)

let alignof_proxy tagDefs =
  alignof ~tagDefs
