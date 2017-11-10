open Defacto_memory_types2
open Mem
open Mem_common

open Core_ctype
open AilTypes
open Nat_big_num

open Either


module type Implementation = sig
  val name: string
  val details: string
  val char_is_signed: bool
  val sizeof_ity: integerType -> int option
  val sizeof_fty: floatingType -> int option
  val alignof_ity: integerType -> int option
end


module DefaultImpl: Implementation = struct
  let name = "clang9_x86_64-apple-darwin16.7.0"
  let details = "Apple LLVM version 9.0.0 (clang-900.0.38)\nTarget: x86_64-apple-darwin16.7.0"
  
  let char_is_signed =
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
end

module Impl = DefaultImpl


let rec simplify_integer_value_base ival_ =
  let lifted_self x =
    either_case (fun n -> IVconcrete n) (fun z -> z) (simplify_integer_value_base x) in
    match ival_ with
      | IVunspecified
      | IVconcurRead _
      | IVconcrete _ ->
          Right ival_
      | IVaddress alloc_id ->
          Right ival_
      | IVfromptr (ty, ity, ptrval) ->
          (* TODO *)
          Right ival_
    | IVop (iop, [ival_1; ival_2]) ->
        let num_op = match iop with
          | IntAdd ->
              add
          | IntSub ->
              sub
          | IntMul ->
              mul
          | IntDiv ->
              fun x y -> if equal y (of_int 0) then of_int 0 else integerDiv_t x y
          | IntRem_t ->
              fun x y -> if equal y (of_int 0) then of_int 0 else integerRem_t x y
          | IntRem_f ->
              fun x y -> if equal y (of_int 0) then of_int 0 else integerRem_f x y
          | IntExp ->
              fun x y -> pow_int x (Pervasives.abs (to_int y))
        in
        begin match (simplify_integer_value_base ival_1, simplify_integer_value_base ival_2) with
          | (Left n1, Left n2) ->
              Left (num_op n1 n2)
          | (x, y) ->
              let f = either_case (fun z -> IVconcrete z) (fun z -> z) in
              Right (IVop (iop, [f x; f y]))
        end
    | IVop _ ->
        (* Core type error *)
        assert false
    | IVmin ity ->
        begin match ity with
          | Char ->
              if Impl.char_is_signed then
                Left (negate (pow_int (of_int 2) (8-1)))
              else
                Left (of_int 0)
          | Bool
          | Size_t
          | Unsigned _ ->
              (* all of these are unsigned *)
              Left (of_int 0)
          | Ptrdiff_t
          | Signed _ ->
              (* and all of these are signed *)
              begin match Impl.sizeof_ity ity with
                | Some n ->
                    Left (negate (pow_int (of_int 2) (8*n-1)))
                | None ->
                    Right ival_
              end
          | Enum _
          | IBuiltin _ ->
              failwith "IVmin Enum, Builtin"
        end
    | IVmax ity ->
        begin match Impl.sizeof_ity ity with
          | Some n ->
              Left (sub (pow_int (of_int 2) (8*n-1)) (of_int 1))
          | None ->
              Right ival_
        end
    | IVsizeof ty ->
        begin match ty with
          | Void0 ->
              (* Ail type error *)
              assert false
          | Basic0 (Integer ity) ->
              begin match Impl.sizeof_ity ity with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Basic0 (Floating fty) ->
              begin match Impl.sizeof_fty fty with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Array0 (elem_ty, None) ->
              (* Ail type error *)
              assert false
          | Array0 (elem_ty, Some n) ->
              simplify_integer_value_base (IVop (IntMul, [IVsizeof elem_ty; IVconcrete n]))
          | Function0 _ ->
              (* Ail type error *)
              assert false
          | Pointer0 (_, ref_ty) ->
              Left (of_int 8)
          | Atomic0 atom_ty ->
              simplify_integer_value_base (IVsizeof atom_ty)
          | Struct0 tag_sym ->
              (* TODO: PADDINGS!! *)
              let membrs = Pmap.find tag_sym (Tags.tagDefs ()) in
              simplify_integer_value_base begin
                List.fold_left (fun acc (_, ty) ->
                  IVop (IntAdd, [lifted_self (IVsizeof ty); acc])
                ) (IVconcrete (of_int 0)) membrs
              end
          | Union0 tag_sym ->
              failwith "TODO simplify_integer_value: IVsizeof Union"
          | Builtin0 str ->
              failwith "TODO simplify_integer_value: IVsizeof Builtin"
        end
    | IValignof ty ->
        begin match ty with
          | Void0 ->
              (* Ail type error *)
              assert false
          | Basic0 (Integer ity) ->
              begin match Impl.alignof_ity ity with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Basic0 (Floating fty) ->
              begin match failwith "Impl.alignof_fty fty" with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Array0 (elem_ty, _) ->
              simplify_integer_value_base (IValignof elem_ty)
          | Function0 _ ->
              (* Ail type error *)
              assert false
          | Pointer0 (_, ref_ty) ->
              Left (of_int 8)
          | Atomic0 atom_ty ->
              simplify_integer_value_base (IValignof atom_ty)
          | Struct0 tag_sym ->
              (* TODO *)
              Right ival_
          | Union0 tag_sym ->
              failwith "TODO simplify_integer_value: IValignof Union"
          | Builtin0 str ->
              failwith "TODO simplify_integer_value: IValignof Builtin"
        end
    | IVoffsetof (tag_sym, memb_ident) ->
        failwith "simplify_integer_value: IVoffsetof"
    | IVptrdiff (ptrval1, ptrval2) ->
        (* TODO: check *)
        Right ival_

    | IVbyteof _
    | IVcomposite _ ->
        failwith "simplify_integer_value: IVbyteof, IVcomposite"
    | IVbitwise (ity, BW_complement ival_1) ->
        failwith "simplify_integer_value: IVbyteof, BW_complement"
    | IVbitwise (ity, BW_AND (ival_1, ival_2)) ->
        failwith "simplify_integer_value: IVbyteof, BW_AND"
    | IVbitwise (ity, BW_OR (ival_1, ival_2)) ->
        failwith "simplify_integer_value: IVbyteof, BW_OR"
    | IVbitwise (ity, BW_XOR (ival_1, ival_2)) ->
        failwith "simplify_integer_value: IVbyteof, BW_XOR"


let simplify_integer_value (IV (prov, ival_)) : (num, integer_value) either =
  match simplify_integer_value_base ival_ with
    | Left n ->
        Left n
    | Right ival_' ->
        Right (IV (prov, ival_'))
