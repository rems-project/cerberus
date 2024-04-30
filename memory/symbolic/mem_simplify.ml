open Defacto_memory_types
(* open Mem *)
open Mem_common

open Ctype
open Nat_big_num

open Either

(*open Ocaml_implementation*)


let simple_fromptr =
  false (* false = fromptr is an uninterpreted function for Z3 + the sizeof/_Alignof of
           (u)intptr_t and unsigned long are left symbolic *)



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
              fun x y -> pow_int x (Stdlib.abs (to_int y))
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
              if (Ocaml_implementation.get()).is_signed_ity Char then
                Left (negate (pow_int (of_int 2) (8-1)))
              else
                Left (of_int 0)
          | Bool
          | Size_t ->
              (* all of these are unsigned *)
              Left (of_int 0)
          | Unsigned ibty ->
              if not simple_fromptr && (ibty = Long || ibty = Intptr_t) then
                Right ival_
              else
                (* all of these are unsigned *)
              Left (of_int 0)
          | Ptrdiff_t ->
              (* and all of these are signed *)
              begin match (Ocaml_implementation.get()).sizeof_ity ity with
                | Some n ->
                    Left (negate (pow_int (of_int 2) (8*n-1)))
                | None ->
                    Right ival_
              end
          | Ptraddr_t ->
              Left (of_int 0)

          | Signed ibty ->
              if not simple_fromptr && ibty = Intptr_t then
                  Right ival_
              else
                (* and all of these are signed *)
                begin match (Ocaml_implementation.get()).sizeof_ity ity with
                  | Some n ->
                      Left (negate (pow_int (of_int 2) (8*n-1)))
                  | None ->
                      Right ival_
                end
          | Wchar_t
          | Wint_t ->
              assert false (* TODO *)
          | Enum _ ->
              failwith "IVmin Enum"
        end
    
    | IVmax ity ->
        if   not simple_fromptr
          && (ity = Unsigned Long || ity = Unsigned Intptr_t || ity = Signed Intptr_t) then
          Right ival_
        else begin match (Ocaml_implementation.get()).sizeof_ity ity with
          | Some n ->
              let signed_max =
                (sub (pow_int (of_int 2) (8*n-1)) (of_int 1)) in
              let unsigned_max =
                (sub (pow_int (of_int 2) (8*n)) (of_int 1)) in
              begin match ity with
                | Char ->
                    Left (if (Ocaml_implementation.get()).is_signed_ity Char then
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
                | Ptraddr_t ->
                    Left unsigned_max
                | Enum _ ->
                    failwith "IVmax Enum"
                | Wchar_t
                | Wint_t ->
                    assert false (* TODO *)
              end
          | None ->
              Right ival_
        end

    | IVsizeof (Ctype (_, ty)) ->
        begin match ty with
          | Void ->
              (* Ail type error *)
              assert false
          | Basic (Integer ity) ->
              begin match (Ocaml_implementation.get()).sizeof_ity ity with
                | Some n ->
                    Left (of_int n)
                | None ->
                    prerr_endline (String_core_ctype.string_of_ctype (Ctype ([], ty)));
                    Right ival_
              end
          | Basic (Floating fty) ->
              begin match (Ocaml_implementation.get()).sizeof_fty fty with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Array (elem_ty, None) ->
              (* Ail type error *)
              assert false
          | Array (elem_ty, Some n) ->
              simplify_integer_value_base (IVop (IntMul, [IVsizeof elem_ty; IVconcrete n]))
          | Function _
          | FunctionNoParams _ ->
              (* Ail type error *)
              assert false
          | Pointer (_, ref_ty) ->
              Left (of_int 8)
          | Atomic atom_ty ->
              simplify_integer_value_base (IVsizeof atom_ty)
          | Struct tag_sym ->
              let membrs = match Pmap.find tag_sym (Tags.tagDefs ()) with
                | _, StructDef (membrs, None) ->
                    membrs
                | _, StructDef (membrs, Some (FlexibleArrayMember (attrs, ident, qs, elem_ty))) ->
                    membrs @ [(ident, (attrs, None, qs, Ctype ([], Array (elem_ty, None))))]
                | _ -> assert false
              in
              simplify_integer_value_base begin
                List.fold_left (fun acc (ident, (_, _, _, ty)) ->
                  IVop (IntAdd, [lifted_self (IVsizeof ty); IVop (IntAdd, [IVpadding (tag_sym, ident);  acc])])
                ) (IVconcrete (of_int 0)) membrs
              end
          | Union tag_sym ->
              (* TODO: clean *)
              (* NOTE: the size of a union type is maximum size among its
                 members PLUS some padding to make it so that the address
                 just one past the union respect it's own alignment constraint
                 (i.e. we wan't to be able to have arrays of unions) *)
              let membrs = match Pmap.find tag_sym (Tags.tagDefs ()) with
                | _, UnionDef membrs -> membrs
                | _ -> assert false
              in
              let align =
                match simplify_integer_value_base (IValignof (Ctype ([], Union tag_sym))) with
                  | Left n ->
                      n
                  | Right _ ->
                      assert false
              in
              begin match List.map (fun (memb_ident, (_, _, _, ty)) ->
                  match simplify_integer_value_base (IVsizeof ty) with
                    | Left n ->
                        n
                    | Right _ ->
                        failwith ("all the types used by members of a union type\
                                   must have their sizeof constraint specified in\
                                   the implementation. Please specify _Alignof(" ^
                                  String_core_ctype.string_of_ctype ty)
                ) membrs with
              | [] -> assert false
              | size::sizes ->
                let max_size = List.fold_left (fun acc z -> max z acc) size sizes in
                Left (add max_size (sub align (integerRem_f max_size align)))
              end
        end
    | IValignof (Ctype (_, ty)) ->
        begin match ty with
          | Void ->
              (* Ail type error *)
              assert false
          | Basic (Integer ity) ->
              begin match (Ocaml_implementation.get()).alignof_ity ity with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Basic (Floating fty) ->
              begin match (Ocaml_implementation.get()).alignof_fty fty with
                | Some n ->
                    Left (of_int n)
                | None ->
                    Right ival_
              end
          | Array (elem_ty, _) ->
              simplify_integer_value_base (IValignof elem_ty)
          | Function _
          | FunctionNoParams _ ->
              (* Ail type error *)
              assert false
          | Pointer (_, ref_ty) ->
              Left (of_int 8)
          | Atomic atom_ty ->
              simplify_integer_value_base (IValignof atom_ty)
          | Struct tag_sym ->
              (* This is done in Smt, because we need to actually generate constraints *)
              Right ival_
          | Union tag_sym ->
              (* NOTE: these two partial patterns are ok by typing of Ail *)
              let membrs = match Pmap.find tag_sym (Tags.tagDefs ()) with
                | _, UnionDef membrs -> membrs
                | _ -> assert false
              in
              begin match List.map (fun (memb_ident, (_, align_opt, _, ty)) ->
                  let align_iv =
                    match align_opt with
                      | None ->
                        IValignof ty
                      | Some (AlignInteger al_n) ->
                          IVconcrete al_n
                      | Some (AlignType al_ty) ->
                        IValignof al_ty in
                  match simplify_integer_value_base align_iv with
                    | Left n ->
                        n
                    | Right _ ->
                        failwith ("all the types used by members of a union type\
                                   must have their alignment constraint specified in\
                                   the implementation. Please specify _Alignof(" ^
                                  String_core_ctype.string_of_ctype ty)
                ) membrs with
                | [] -> assert false
                | (n::ns) ->
                  (* NOTE: the alignment constraint of a union type is the largest
                     alignment constraint of any of its member *)
                  Left (List.fold_left (fun acc z -> max z acc) n ns)
              end
        end
    | IVoffsetof (tag_sym, memb_ident) ->
        failwith "simplify_integer_value: IVoffsetof"
    | IVpadding _ ->
        Right ival_
    | IVptrdiff (ty, ptrval1, ptrval2) ->
        (* TODO: check *)
        Right ival_

    | IVbyteof (ival_, mval) ->
        begin match (ival_, mval) with
          | (IVconcrete n, MVcomposite (xs, mval')) ->
              let pred = function
                | IVconcrete n' when n = n' -> true
                | _ -> false in
              begin match List.find_opt (fun (z, _) -> pred z) xs with
                | Some (_, IV (_, ival_')) ->
                    simplify_integer_value_base ival_'
                | None ->
                    failwith "Mem_simplify, IVbyteof ==> need to look inside a MVcomposite"
              end
          | _ ->
              failwith ("Mem_simplify, IVbyteof ==> " ^
                        String_defacto_memory.string_of_integer_value (IV (Prov_none, ival_)) ^
                        " -- " ^ String_defacto_memory.string_of_mem_value mval)

        end
(*
        (* TODO/NOTE: assuming little endian two's complement encoding *)
*)
(*
let byteof i n = let n' = n `div` (2 ^ (i * 8)) in mod n' 256
*)

        
        
    | IVcomposite _ ->
        failwith "simplify_integer_value: IVcomposite"
    | IVbitwise (ity, BW_complement ival_1) ->
        begin match ((Ocaml_implementation.get()).sizeof_ity ity, simplify_integer_value_base ival_1) with
          | (Some width, Left n1) ->
              Left (Defacto_memory_aux.tmp_compl width n1)
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


let simplify_integer_value (IV (prov, ival_)) : (num, impl_integer_value) either =
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
