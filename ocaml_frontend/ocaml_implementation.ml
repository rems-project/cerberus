open Ctype

type implementation = {
  name: string;
  details: string;
  sizeof_pointer: int option;
  alignof_pointer: int option;
  is_signed_ity: integerType -> bool;
  sizeof_ity: integerType -> int option;
  precision_ity: integerType -> int option;
  sizeof_fty: floatingType -> int option;
  alignof_ity: integerType -> int option;
  alignof_fty: floatingType -> int option;
  register_enum: Symbol.sym -> Nat_big_num.num list -> bool;
  typeof_enum: Symbol.sym -> integerType;
}


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

  (* NOTE: some of them are not implementation defined *)
  let is_signed_ity ity =
    let ity' =
      match ity with
        | Enum tag_sym ->
            typeof_enum tag_sym
        | _ ->
            ity in
    match ity' with
      | Char ->
          true
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

  let sizeof_ity = function
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
          | IntN_t n
          | Int_leastN_t n
          | Int_fastN_t n ->
              n/8
          | Intmax_t
          | Intptr_t ->
              8
        end
    | Enum ident ->
        (* TODO *)
        Some 4
    | Wchar_t
    | Wint_t ->
        Some 4
    | Size_t
    | Ptrdiff_t ->
        Some 8
  
  (* NOTE: the code is bit generic here to allow reusability *)
  let precision_ity ity =
    match sizeof_ity ity with
    | Some n ->
      if is_signed_ity ity then
        Some (8*n-1)
      else
        Some (8*n)
    | None ->
      None

  let sizeof_fty = function
    | RealFloating Float ->
        Some 8 (* TODO:hack ==> 4 *)
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 8 (* TODO:hack ==> 16 *)

  let alignof_ity = function
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
          | IntN_t n
          | Int_leastN_t n
          | Int_fastN_t n ->
              n/8
          | Intmax_t
          | Intptr_t ->
              8
        end
    | Enum ident ->
        (* TODO *)
        Some 4
    | Wchar_t
    | Wint_t ->
        Some 4
    | Size_t
    | Ptrdiff_t ->
        Some 8

  let alignof_fty = function
    | RealFloating Float ->
        Some 8 (* TODO:hack ==> 4 *)
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 8 (* TODO:hack ==> 16 *)
  
  let impl: implementation = {
    name;
    details;
    sizeof_pointer;
    alignof_pointer;
    is_signed_ity;
    sizeof_ity;
    precision_ity;
    sizeof_fty;
    alignof_ity;
    alignof_fty;
    register_enum;
    typeof_enum;
  }
end


module DefactoImpl = struct
  include DefaultImpl

  let sizeof_ity = function
    | Signed Intptr_t
    | Unsigned Intptr_t ->
        None
    | ity ->
        DefaultImpl.sizeof_ity ity
end


(* LP64 *)
module HafniumImpl = struct
  let name = "hafnium_aarch64-none-eabi"
  let details = "TODO"
  
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
          failwith ("Hafnium impl => typeof_enum: '" ^
                    Symbol.instance_Show_Show_Symbol_sym_dict.show_method tag_sym ^ "' was not registered")
      | Some (_, z) ->
          z
  
  let rec is_signed_ity = function
    | Char ->
        false
    | Bool ->
        false
    | Signed _ ->
        true
    | Unsigned _ ->
        false
    | Enum tag_sym ->
        is_signed_ity (typeof_enum tag_sym)
    | Wchar_t ->
        true
    | Wint_t ->
        failwith "Hafnium is_signed Wint_t"
    | Size_t ->
        (* STD *)
        false
    | Ptrdiff_t ->
        (* STD *)
        true
  
  let sizeof_ity = function
    | Char ->
        Some 1
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
          | IntN_t n
          | Int_leastN_t n
          | Int_fastN_t n ->
              n/8
          | Intmax_t
          | Intptr_t ->
              8
        end
    | Enum _ ->
        (* signed or unsigned int *)
        Some 4
    | Wchar_t ->
        Some 4
    | Wint_t ->
        failwith "Hafnium sizeof Wint_t"
    | Size_t ->
        Some 8
    | Ptrdiff_t ->
        Some 8
  
  (* No trap representations *)
  let precision_ity ity =
    match sizeof_ity ity with
    | Some n ->
      if is_signed_ity ity then
        Some (8*n-1)
      else
        Some (8*n)
    | None ->
      None
  
  let sizeof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16
  
  let alignof_ity = function
    | Char ->
        Some 1
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
          | IntN_t n
          | Int_leastN_t n
          | Int_fastN_t n ->
              n/8
          | Intmax_t
          | Intptr_t ->
              8
        end
    | Enum _ ->
        (* signed or unsigned int *)
        Some 4
    | Wchar_t ->
        Some 4
    | Wint_t ->
        failwith "Hafnium alignof Wint_t"
    | Size_t ->
        Some 8
    | Ptrdiff_t ->
        Some 8
  
  let alignof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16

  let impl: implementation = {
    name;
    details;
    sizeof_pointer;
    alignof_pointer;
    is_signed_ity;
    sizeof_ity;
    precision_ity;
    sizeof_fty;
    alignof_ity;
    alignof_fty;
    register_enum;
    typeof_enum;
  }
end


let hafniumIntImpl: IntegerImpl.implementation =
  let open IntegerImpl in
  make_implementation Two'sComplement 
  HafniumImpl.is_signed_ity
  (fun ity ->
    match HafniumImpl.precision_ity ity with
      | Some n -> n
      | None   -> assert false)
  (Size_t)
  (Ptrdiff_t)


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
