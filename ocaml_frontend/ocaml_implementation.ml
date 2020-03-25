open Ctype

module type Implementation = sig
  val name: string
  val details: string
  val sizeof_pointer: int option
  val alignof_pointer: int option
  val is_signed_ity: integerType -> bool
  val sizeof_ity: integerType -> int option
  val precision_ity: integerType -> int option
  val sizeof_fty: floatingType -> int option
  val alignof_ity: integerType -> int option
  val alignof_fty: floatingType -> int option
  val register_enum: Symbol.sym -> Nat_big_num.num list -> bool
  val typeof_enum: Symbol.sym -> integerType
end


module DefaultImpl: Implementation = struct
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
  let rec is_signed_ity = function
    | Char ->
        true
    | Bool ->
        false
    | Signed _ ->
        true
    | Unsigned _ ->
        false
    | Enum tag_sym ->
        is_signed_ity (typeof_enum tag_sym)
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
module HafniumImpl : Implementation = struct
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


module Impl = DefaultImpl
