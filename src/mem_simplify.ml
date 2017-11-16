open Defacto_memory_types2
open Mem
open Mem_common

open Core_ctype
open AilTypes
open Nat_big_num

open Either

open Ocaml_implementation



let rec simplify_integer_value_base ival_ =
  let lifted_self x =
    either_case (fun n -> IVconcrete n) (fun z -> z) (simplify_integer_value_base x) in
    match ival_ with
      | IVunspecified
      | IVconcurRead _ ->
          Right ival_
      | IVconcrete n ->
          Left n
      | IVaddress (alloc_id, pref) ->
          Right ival_
      | IVfromptr (ty, ity, ptrval, sh) ->
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
          (* TMP *)
          | Unsigned Long
          | Unsigned Intptr_t
          | Signed Intptr_t ->
              Right ival_
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
    
    (* TMP *)
    | IVmax (Unsigned Long)
    | IVmax (Unsigned Intptr_t)
    | IVmax (Signed Intptr_t) ->
        Right ival_
    
    | IVmax ity ->
        begin match Impl.sizeof_ity ity with
          | Some n ->
              let signed_max =
                (sub (pow_int (of_int 2) (8*n-1)) (of_int 1)) in
              let unsigned_max =
                (sub (pow_int (of_int 2) (8*n)) (of_int 1)) in
              begin match ity with
                | Char ->
                    Left (if Impl.char_is_signed then
                      signed_max
                    else
                      unsigned_max)
                | Bool ->
                    (* TODO: not sure about this (maybe it should be 1 and not 255? *)
                    Left unsigned_max
                | Size_t
                | Unsigned _ ->
                    Left unsigned_max
                | Ptrdiff_t
                | Signed _ ->
                    Left signed_max
                | Enum _ ->
                    failwith "IVmax Enum"
                | IBuiltin _ ->
                    failwith "IVmax IBuiltin"
              end
          | None ->
              Right ival_
        end

(*
        begin match Impl.sizeof_ity ity with
          | Some n ->
              Left (sub (pow_int (of_int 2) (8*n-1)) (of_int 1))
          | None ->
              Right ival_
        end
*)
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
              let Tags.StructDef membrs = Pmap.find tag_sym (Tags.tagDefs ()) in
              simplify_integer_value_base begin
                List.fold_left (fun acc (ident, ty) ->
                  IVop (IntAdd, [lifted_self (IVsizeof ty); IVop (IntAdd, [IVpadding (tag_sym, ident);  acc])])
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
              begin match Impl.alignof_fty fty with
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
              (* This is done in Smt, because we need to actually generate constraints *)
              Right ival_
          | Union0 tag_sym ->
              failwith "TODO simplify_integer_value: IValignof Union"
          | Builtin0 str ->
              failwith "TODO simplify_integer_value: IValignof Builtin"
        end
    | IVoffsetof (tag_sym, memb_ident) ->
        failwith "simplify_integer_value: IVoffsetof"
    | IVpadding _ ->
        Right ival_
    | IVptrdiff (ty, ptrval1, ptrval2) ->
        (* TODO: check *)
        Right ival_

    | IVbyteof _
    | IVcomposite _ ->
        failwith "simplify_integer_value: IVbyteof, IVcomposite"
    | IVbitwise (ity, BW_complement ival_1) ->
        begin match (Impl.sizeof_ity ity, simplify_integer_value_base ival_1) with
          | (Some width, Left n1) ->
              Left (Defacto_memory_aux2.tmp_compl width n1)
          | (_, x) ->
              let f = either_case (fun z -> IVconcrete z) (fun z -> z) in
              Right (IVbitwise (ity, BW_complement (f x)))
        end
    | IVbitwise (ity, BW_AND (ival_1, ival_2)) ->
        begin match (simplify_integer_value_base ival_1, simplify_integer_value_base ival_2) with
          | (Left n1, Left n2) ->
              Left (Nat_big_num.bitwise_and n1 n2)
          | (x, y) ->
              let f = either_case (fun z -> IVconcrete z) (fun z -> z) in
              Right (IVbitwise (ity, BW_AND (f x, f y)))
        end
    | IVbitwise (ity, BW_OR (ival_1, ival_2)) ->
        begin match (simplify_integer_value_base ival_1, simplify_integer_value_base ival_2) with
          | (Left n1, Left n2) ->
              Left (Nat_big_num.bitwise_or n1 n2)
          | (x, y) ->
              let f = either_case (fun z -> IVconcrete z) (fun z -> z) in
              Right (IVbitwise (ity, BW_OR (f x, f y)))
        end
    | IVbitwise (ity, BW_XOR (ival_1, ival_2)) ->
        begin match (simplify_integer_value_base ival_1, simplify_integer_value_base ival_2) with
          | (Left n1, Left n2) ->
              Left (Nat_big_num.bitwise_xor n1 n2)
          | (x, y) ->
              let f = either_case (fun z -> IVconcrete z) (fun z -> z) in
              Right (IVbitwise (ity, BW_XOR (f x, f y)))
        end


let lifted_simplify_integer_value_base ival_ =
  Either.either_case
    (fun n -> IVconcrete n)
    (fun z -> z)
    (simplify_integer_value_base ival_)


let simplify_integer_value (IV (prov, ival_)) : (num, integer_value) either =
  match simplify_integer_value_base ival_ with
    | Left n ->
        Left n
    | Right ival_' ->
        Right (IV (prov, ival_'))



(*
let simplify_mem_constraint constr =
  let lift = either_case (fun z -> (IV (Prov_none, IVconcrete z))) (fun z -> z) in
  let simplify_binary acc op ival_1 ival_2 =
    begin match (simplify_integer_value ival_1, simplify_integer_value ival_2) with
      | (Left n1, Left n2) ->
          if n1 = n2 then
            Some acc
          else
            None
      | (x, y) ->
          Some (MC_eq (lift x, lift y) :: acc)
    end in
  let rec aux _acc constr =
    match _acc with
      | None ->
          None
      | Some acc ->
          begin match constr with
            | MC_empty ->
                _acc
            | MC_eq (ival_1, ival_2) ->
                simplify_binary acc (=) ival_1 ival_2
            | MC_le (ival_1, ival_2) ->
                simplify_binary acc (<=) ival_1 ival_2
            | MC_lt (ival_1, ival_2) ->
                simplify_binary acc (<) ival_1 ival_2
            | MC_or (constr1, constr2) ->
                begin match (aux (Some []) constr1, aux (Some []) constr2) with
                  | (None, Some cs)
                  | (Some cs, None) ->
                      Some (cs @ acc)
                  | (None, None) ->
                      None
                  | (Some cs1, Some cs2) ->
                      Some (MC_or (MC_conj cs1, MC_conj cs2) :: acc)
                end
            | MC_conj constrs ->
                List.fold_left aux _acc constrs
            | MC_not _ ->
                (* TODO *)
                Some (constr :: acc)
          end
  in
  match aux (Some []) constr with
    | None ->
        MC_empty
    | Some constrs ->
        MC_conj constrs


*)
