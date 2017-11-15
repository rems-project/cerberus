open AilTypes

module type Implementation = sig
  val name: string
  val details: string
  val char_is_signed: bool
  val sizeof_pointer: int option
  val sizeof_ity: integerType -> int option
  val sizeof_fty: floatingType -> int option
  val alignof_ity: integerType -> int option
  val alignof_fty: floatingType -> int option
end


module DefaultImpl: Implementation = struct
  let name = "clang9_x86_64-apple-darwin16.7.0"
  let details = "Apple LLVM version 9.0.0 (clang-900.0.38)\nTarget: x86_64-apple-darwin16.7.0"
  
  let char_is_signed =
    true
  
  let sizeof_pointer =
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
end

module Impl = DefaultImpl
