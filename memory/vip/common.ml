(* Things mostly taken unchanged from the concrete memory model that
   we might want to put in a common module *)
open Ctype

let ident_equal x y =
  Symbol.instance_Basic_classes_Eq_Symbol_identifier_dict.isEqual_method x y

let rec offsetsof tagDefs tag_sym =
  match Pmap.find tag_sym tagDefs with
    | _, StructDef (membrs_, flexible_opt) ->
        (* NOTE: the offset of a flexible array member is just like
           that of any other member *)
        let membrs = match flexible_opt with
          | None ->
              membrs_
          | Some (FlexibleArrayMember (attrs, ident, qs, ty)) ->
              membrs_ @ [(ident, (attrs, None, qs, ty))] in
        let (xs, maxoffset) =
          List.fold_left (fun (xs, last_offset) (membr, (_, align_opt, _, ty)) ->
            let size = sizeof ~tagDefs ty in
            let align =
              match align_opt with
                | None ->
                    alignof ~tagDefs ty
                | Some (AlignInteger al_n) ->
                    Z.to_int al_n
                | Some (AlignType al_ty) ->
                  alignof ~tagDefs al_ty in
            let x = last_offset mod align in
            let pad = if x = 0 then 0 else align - x in
            ((membr, ty, last_offset + pad) :: xs, last_offset + pad + size)
          ) ([], 0) membrs in
        (List.rev xs, maxoffset)
    | _, UnionDef membrs ->
        (List.map (fun (ident, (_, _, _, ty)) -> (ident, ty, 0)) membrs, 0)

and sizeof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) =
  match ty with
    | Void | Array (_, None) | Function _ | FunctionNoParams _ ->
        Printf.fprintf stderr "Common.sizeof ==> ty: %s\n"
          (String_core_ctype.string_of_ctype cty);
        assert false
    | Basic (Integer ity) ->
        begin match (Ocaml_implementation.get ()).sizeof_ity ity with
          | Some n ->
              n
          | None ->
              failwith ("the concrete memory model requires a complete implementation sizeof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
        end
    | Basic (Floating fty) ->
        begin match (Ocaml_implementation.get ()).sizeof_fty fty with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation sizeof FLOAT"
        end
    | Array (elem_ty, Some n) ->
        (* TODO: what if too big? *)
        Nat_big_num.to_int n * sizeof ~tagDefs elem_ty
    | Pointer _ ->
        begin match (Ocaml_implementation.get ()).sizeof_pointer with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation sizeof POINTER"
        end
    | Atomic atom_ty ->
        sizeof ~tagDefs atom_ty
    | Struct tag_sym ->
        (* TODO: need to add trailing padding for structs with a flexible array member *)
        Cerb_debug.warn [] (fun () -> "TODO: Concrete.sizeof doesn't add trailing padding for structs with a flexible array member");
        let (_, max_offset) = offsetsof tagDefs tag_sym in
        let align = alignof ~tagDefs cty in
        let x = max_offset mod align in
        if x = 0 then max_offset else max_offset + (align - x)
    | Union tag_sym ->
        begin match Pmap.find tag_sym (Tags.tagDefs ()) with
          | _, StructDef _ ->
              assert false
          | _, UnionDef membrs ->
              let (max_size, max_align) =
                List.fold_left (fun (acc_size, acc_align) (_, (_, align_opt, _, ty)) ->
                  let align =
                    match align_opt with
                      | None ->
                          alignof ~tagDefs ty
                      | Some (AlignInteger al_n) ->
                          Z.to_int al_n
                      | Some (AlignType al_ty) ->
                        alignof ~tagDefs al_ty in
                  (max acc_size (sizeof ~tagDefs ty), max acc_align align)
                ) (0, 0) membrs in
              (* NOTE: adding padding at the end to satisfy the alignment constraints *)
              let x = max_size mod max_align in
              if x = 0 then max_size else max_size + (max_align - x)
        end

and alignof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) =
  match ty with
    | Void ->
        assert false
    | Basic (Integer ity) ->
        begin match (Ocaml_implementation.get ()).alignof_ity ity with
          | Some n ->
              n
          | None ->
              failwith ("the concrete memory model requires a complete implementation alignof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
        end
    | Basic (Floating fty) ->
        begin match (Ocaml_implementation.get ()).alignof_fty fty with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation alignof FLOATING"
        end
    | Array (elem_ty, _) ->
        alignof ~tagDefs elem_ty
    | Function _
    | FunctionNoParams _ ->
        assert false
    | Pointer _ ->
        begin match (Ocaml_implementation.get ()).alignof_pointer with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation alignof POINTER"
        end
    | Atomic atom_ty ->
        alignof ~tagDefs atom_ty
    | Struct tag_sym ->
        begin match Pmap.find tag_sym tagDefs with
          | _, UnionDef _ ->
              assert false
          | _, StructDef (membrs, flexible_opt)  ->
              (* NOTE: we take into account the potential flexible array member by tweaking
                 the accumulator init of the fold. *)
              let init = match flexible_opt with
                | None ->
                    0
                | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
                    alignof ~tagDefs (Ctype ([], Array (elem_ty, None))) in
              (* NOTE: Structs (and unions) alignment is that of the maximum alignment
                 of any of their components. *)
              List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
                let memb_align =
                  match align_opt with
                    | None ->
                        alignof ~tagDefs ty
                    | Some (AlignInteger al_n) ->
                        Z.to_int al_n
                    | Some (AlignType al_ty) ->
                      alignof ~tagDefs al_ty in
                max memb_align acc
              ) init membrs
        end
    | Union tag_sym ->
        begin match Pmap.find tag_sym (Tags.tagDefs ()) with
          | _, StructDef _ ->
              assert false
          | _, UnionDef membrs ->
              (* NOTE: Structs (and unions) alignment is that of the maximum alignment
                 of any of their components. *)
              List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
                let memb_align =
                  match align_opt with
                    | None ->
                        alignof ~tagDefs ty
                    | Some (AlignInteger al_n) ->
                        Z.to_int al_n
                    | Some (AlignType al_ty) ->
                      alignof ~tagDefs al_ty in
                max memb_align acc
              ) 0 membrs
        end

let ity_max ity =
  let open Nat_big_num in
  match (Ocaml_implementation.get ()).sizeof_ity ity with
    | Some n ->
        let signed_max =
          sub (pow_int (of_int 2) (8*n-1)) (of_int 1) in
        let unsigned_max =
          sub (pow_int (of_int 2) (8*n)) (of_int 1) in
        let ity = match ity with
          | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
          | _ -> ity
        in
        begin match ity with
          | Char ->
              if (Ocaml_implementation.get ()).is_signed_ity Char then
                signed_max
              else
                unsigned_max
          | Bool ->
              (* TODO: not sure about this (maybe it should be 1 and not 255? *)
              unsigned_max
          | Size_t
          | Wchar_t (* TODO: it is implementation defined if unsigned *)
          | Unsigned _ ->
              unsigned_max
          | Ptrdiff_t
          | Wint_t (* TODO *)
          | Signed _ ->
              signed_max
          |  Ptraddr_t ->
              unsigned_max
          | Enum nm ->
              assert false
        end
    | None ->
        failwith "the VIP memory model requires a complete implementation MAX"

let ity_min ity =
  let open Nat_big_num in
  let ity = match ity with
    | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
    | _ -> ity
  in
  match ity with
    | Char ->
        if (Ocaml_implementation.get ()).is_signed_ity Char then
          negate (pow_int (of_int 2) (8-1))
        else
          zero
    | Bool
    | Size_t
    | Wchar_t (* TODO: it is implementation defined if unsigned *)
    | Wint_t
    | Unsigned _ ->
        (* all of these are unsigned *)
        zero
    | Ptrdiff_t
    | Signed _ ->
        (* and all of these are signed *)
        begin match (Ocaml_implementation.get ()).sizeof_ity ity with
          | Some n ->
              negate (pow_int (of_int 2) (8*n-1))
          | None ->
              failwith "the VIP memory model requires a complete implementation MIN"
        end
    | Ptraddr_t -> zero
    | Enum _ ->
        assert false
