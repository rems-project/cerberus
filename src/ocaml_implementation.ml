open AilTypes

module type Implementation = sig
  val name: string
  val details: string
  val char_is_signed: bool
  val sizeof_pointer: int option
  val alignof_pointer: int option
  val sizeof_ity: integerType -> int option
  val sizeof_fty: floatingType -> int option
  val alignof_ity: integerType -> int option
  val alignof_fty: floatingType -> int option
  val register_enum: Symbol.sym -> Nat_big_num.num list -> bool
  val typeof_enum: Symbol.sym -> integerType option
end


module DefaultImpl: Implementation = struct
  let name = "clang9_x86_64-apple-darwin16.7.0"
  let details = "Apple LLVM version 9.0.0 (clang-900.0.38)\nTarget: x86_64-apple-darwin16.7.0"
  
  let char_is_signed =
    true
  
  let sizeof_pointer =
    Some 8
  let alignof_pointer =
    Some 8
  
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
    | IBuiltin str ->
        (* TODO *)
        None
    | Enum ident ->
        (* TODO *)
        None
    | Size_t
    | Ptrdiff_t ->
        Some 8
  
  let sizeof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16
  
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
    | IBuiltin str ->
        (* TODO *)
        None
    | Enum ident ->
        (* TODO *)
        None
    | Size_t
    | Ptrdiff_t ->
        Some 8
  
  
  let alignof_fty = function
    | RealFloating Float ->
        Some 4
    | RealFloating Double ->
        Some 8
    | RealFloating LongDouble ->
        Some 16
  
  
  (* INTERNAL *)
  let registered_enums =
    ref []
  
  let sym_eq =
    Symbol.instance_Basic_classes_Eq_Symbol_sym_dict.isEqual_method
  
  (* NOTE: for enums implementation we follow GCC, since Clang doesn't document
     it's implementation details... *)
  let register_enum tag_sym ns =
    (* NOTE: we don't support GCC's -fshort-enums option *)
    let ity =
      if List.exists (fun n -> Nat_big_num.less n Nat_big_num.zero) ns then
        Signed Int_
      else
        Unsigned Int_ in
    if List.exists (fun (z, _) -> sym_eq z tag_sym) !registered_enums then
      false
    else begin
      registered_enums := (tag_sym, ity) :: !registered_enums;
      true
    end

  let typeof_enum tag_sym =
    match List.find_opt (fun (z, _) -> sym_eq z tag_sym) !registered_enums with
      | None        -> None
      | Some (_, z) -> Some z
end

module Impl = DefaultImpl


module DefactoImpl = struct
  include DefaultImpl
  
  let sizeof_ity = function
    | Signed Intptr_t
    | Unsigned Intptr_t ->
        None
    | ity ->
        DefaultImpl.sizeof_ity ity
end
