module CF = Cerb_frontend

(* module CB=Cerb_backend
   open CB.Pipeline
   open Setup *)
open CF.Cn
open Compile
open Executable_spec_utils
module A = CF.AilSyntax
module C = CF.Ctype
module BT = BaseTypes
module IT = IndexTerms
module T = Terms
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
module AT = ArgumentTypes
module OE = Ownership_exec

let true_const = A.AilEconst (ConstantPredefined PConstantTrue)

let ownership_ctypes = ref []

let rec cn_base_type_to_bt = function
  | CN_unit -> BT.Unit
  | CN_bool -> BT.Bool
  | CN_integer -> BT.Integer
  | CN_bits (sign, size) ->
    BT.Bits ((match sign with CN_unsigned -> BT.Unsigned | CN_signed -> BT.Signed), size)
  | CN_real -> BT.Real
  | CN_loc -> BT.Loc ()
  | CN_alloc_id -> BT.Alloc_id
  | CN_struct tag -> BT.Struct tag
  | CN_datatype tag -> BT.Datatype tag
  | CN_record ms ->
    let ms' = List.map (fun (id, bt) -> (id, cn_base_type_to_bt bt)) ms in
    BT.Record ms'
  | CN_map (type1, type2) -> BT.Map (cn_base_type_to_bt type1, cn_base_type_to_bt type2)
  | CN_list typ -> cn_base_type_to_bt typ
  | CN_tuple ts -> BT.Tuple (List.map cn_base_type_to_bt ts)
  | CN_set typ -> cn_base_type_to_bt typ
  | CN_user_type_name _ -> failwith "TODO CN_user_type_name"
  | CN_c_typedef_name _ -> failwith "TODO CN_c_typedef_name"


module MembersKey = struct
  type t = (Id.t * Sym.t cn_base_type) list

  let rec compare (ms : t) ms' =
    match (ms, ms') with
    | [], [] -> 0
    | _, [] -> 1
    | [], _ -> -1
    | (id, cn_bt) :: ms, (id', cn_bt') :: ms' ->
      let c = String.compare (Id.s id) (Id.s id') in
      if c == 0 then (
        let c' =
          BaseTypes.compare (cn_base_type_to_bt cn_bt) (cn_base_type_to_bt cn_bt')
        in
        if c' == 0 then
          compare ms ms'
        else
          c')
      else
        c
end

module RecordMap = Map.Make (MembersKey)

let records = ref RecordMap.empty

let generic_cn_dt_sym = Sym.fresh_pretty "cn_datatype"

let create_id_from_sym ?(lowercase = false) sym =
  let str = Sym.pp_string sym in
  let str = if lowercase then String.lowercase_ascii str else str in
  Id.id str


let create_sym_from_id id = Sym.fresh_pretty (Id.pp_string id)

let generate_sym_with_suffix
  ?(suffix = "_tag")
  ?(uppercase = false)
  ?(lowercase = false)
  constructor
  =
  let str = Sym.pp_string constructor ^ suffix in
  let str = if uppercase then String.uppercase_ascii str else str in
  let str = if lowercase then String.lowercase_ascii str else str in
  Sym.fresh_pretty str


let generate_error_msg_info_update_stats ?(cn_source_loc_opt = None) () =
  let cn_source_loc_arg =
    match cn_source_loc_opt with
    | Some loc ->
      let loc_str = Cerb_location.location_to_string loc in
      let _, loc_str_2 = Cerb_location.head_pos_of_location loc in
      let loc_str_2_escaped =
        Str.global_replace (Str.regexp_string "\n") "\\n" loc_str_2
      in
      let loc_str_2_escaped =
        Str.global_replace (Str.regexp_string "\"") "\'" loc_str_2_escaped
      in
      let cn_source_loc_str =
        mk_expr
          A.(AilEstr (None, [ (Cerb_location.unknown, [ loc_str_2_escaped ^ loc_str ]) ]))
      in
      cn_source_loc_str
    | None -> mk_expr A.(AilEconst ConstantNull)
  in
  let update_fn_sym = Sym.fresh_pretty "update_cn_error_message_info" in
  [ A.(
      AilSexpr
        (mk_expr (AilEcall (mk_expr (AilEident update_fn_sym), [ cn_source_loc_arg ]))))
  ]


let cn_assert_sym = Sym.fresh_pretty "cn_assert"

let generate_cn_assert ?(cn_source_loc_opt = None) ail_expr =
  let assertion_expr_ = A.(AilEcall (mk_expr (AilEident cn_assert_sym), [ ail_expr ])) in
  let assertion_stat = A.(AilSexpr (mk_expr assertion_expr_)) in
  let error_msg_update_stats_ =
    generate_error_msg_info_update_stats ~cn_source_loc_opt ()
  in
  error_msg_update_stats_ @ [ assertion_stat ]


let rec bt_to_cn_base_type = function
  | BT.Unit -> CN_unit
  | Bool -> CN_bool
  | Integer -> CN_integer
  | Bits (sign, size) ->
    CN_bits ((match sign with Unsigned -> CN_unsigned | Signed -> CN_signed), size)
  | Real -> CN_real
  | MemByte -> failwith (__FUNCTION__ ^ ": TODO MemByte")
  | Alloc_id -> CN_alloc_id
  | CType -> failwith (__FUNCTION__ ^ ": TODO Ctype")
  | Loc () -> CN_loc
  | Struct tag -> CN_struct tag
  | Datatype tag -> CN_datatype tag
  | Record member_types ->
    let ms = List.map (fun (id, bt) -> (id, bt_to_cn_base_type bt)) member_types in
    CN_record ms
  | Map (bt1, bt2) -> CN_map (bt_to_cn_base_type bt1, bt_to_cn_base_type bt2)
  | List bt -> CN_list (bt_to_cn_base_type bt)
  | Tuple bts -> CN_tuple (List.map bt_to_cn_base_type bts)
  | Set bt -> CN_set (bt_to_cn_base_type bt)


let str_of_cn_bitvector_type sign size =
  let sign_str = match sign with CN_signed -> "i" | CN_unsigned -> "u" in
  let size_str = string_of_int size in
  sign_str ^ size_str


let str_of_bt_bitvector_type sign size =
  let sign_str = match sign with BT.Signed -> "i" | BT.Unsigned -> "u" in
  let size_str = string_of_int size in
  sign_str ^ size_str


let augment_record_map ?cn_sym bt =
  let sym_prefix = match cn_sym with Some sym' -> sym' | None -> Sym.fresh () in
  match bt_to_cn_base_type bt with
  | CN_record members ->
    (* Augment records map if entry does not exist already *)
    if not (RecordMap.mem members !records) then (
      let sym' = generate_sym_with_suffix ~suffix:"_record" sym_prefix in
      records := RecordMap.add members sym' !records)
  | _ -> ()


let lookup_records_map members =
  match RecordMap.find_opt members !records with
  | Some sym -> sym
  | None ->
    failwith
      ("Record not found in map ("
       ^ String.concat
           ", "
           (List.map
              (fun (x, cbt) ->
                Pp.(plain (BT.pp (cn_base_type_to_bt cbt) ^^ space ^^ Id.pp x)))
              members)
       ^ ")")


(* TODO: Complete *)
let rec cn_to_ail_base_type ?pred_sym:(_ = None) cn_typ =
  let generate_ail_array bt = C.(Array (cn_to_ail_base_type bt, None)) in
  let typ =
    match cn_typ with
    | CN_unit -> C.Void
    | CN_bool -> C.(Basic (Integer Bool))
    | CN_integer -> C.(Basic (Integer (Signed Long)))
    (* TODO: Discuss integers *)
    | CN_bits (_sign, _size) -> C.(Basic (Integer (Signed Long)))
    | CN_real -> failwith "TODO CN_real"
    | CN_loc ->
      C.(Pointer (empty_qualifiers, Ctype ([], Void)))
      (* Casting all CN pointers to void star *)
    | CN_alloc_id ->
      C.(Basic (Integer (Signed Long)))
      (* gets replaced with typedef anyway (TODO: clean up) *)
    | CN_struct sym -> C.(Struct (generate_sym_with_suffix ~suffix:"_cn" sym))
    | CN_record members ->
      let sym = lookup_records_map members in
      Struct sym
    (* Every struct is converted into a struct pointer *)
    | CN_datatype sym -> Struct sym
    | CN_map (_, cn_bt) -> generate_ail_array cn_bt
    | CN_list bt ->
      generate_ail_array bt
      (* TODO: What is the optional second pair element for? Have just put None for now *)
    | CN_tuple _ts ->
      failwith (__FUNCTION__ ^ ":Tuples not yet supported")
      (* Printf.printf "Entered CN_tuple case\n"; *)
      (* let some_id = create_id_from_sym (Sym.fresh_pretty "some_sym") in
         let members = List.map (fun t -> (some_id, t)) ts in
         let sym = lookup_records_map members in
         Struct sym *)
    | CN_set bt -> generate_ail_array bt
    | CN_user_type_name _ -> failwith "TODO CN_user_type_name"
    | CN_c_typedef_name _ -> failwith "TODO CN_c_typedef_name"
  in
  let annots =
    match cn_typ with
    | CN_bits (sign, size) ->
      [ CF.Annot.Atypedef
          (Sym.fresh_pretty ("cn_bits_" ^ str_of_cn_bitvector_type sign size))
      ]
    | CN_integer -> [ CF.Annot.Atypedef (Sym.fresh_pretty "cn_integer") ]
    | CN_bool -> [ CF.Annot.Atypedef (Sym.fresh_pretty "cn_bool") ]
    | CN_map _ -> [ CF.Annot.Atypedef (Sym.fresh_pretty "cn_map") ]
    | CN_loc -> [ CF.Annot.Atypedef (Sym.fresh_pretty "cn_pointer") ]
    | CN_alloc_id -> [ CF.Annot.Atypedef (Sym.fresh_pretty "cn_alloc_id") ]
    | _ -> []
  in
  let ret = mk_ctype ~annots typ in
  match typ with C.Void -> ret | _ -> mk_ctype C.(Pointer (empty_qualifiers, ret))


(* Make everything a pointer *)

let bt_to_ail_ctype ?(pred_sym = None) t =
  cn_to_ail_base_type ~pred_sym (bt_to_cn_base_type t)


let cn_to_ail_unop_internal bt =
  let typedef_str_opt = get_typedef_string (bt_to_ail_ctype bt) in
  function
  | IT.Not -> (A.Bnot, Some "cn_bool_not")
  | Negate ->
    (match typedef_str_opt with
     | Some typedef_str -> (A.Bnot, Some (typedef_str ^ "_negate"))
     | None -> failwith "BW_FLS_NoSMT unop translation: typedef string not found")
  | BW_FLS_NoSMT ->
    let failure_msg =
      Printf.sprintf
        "FLS cannot be applied to index term of type %s"
        (Pp.plain (BT.pp bt))
    in
    (match bt with
     | Bits (Unsigned, n) ->
       if n == 64 then
         (A.Bnot, Some "cn_bits_u64_flsl")
       else if n == 32 then
         (A.Bnot, Some "cn_bits_u32_fls")
       else
         failwith failure_msg
     | _ -> failwith failure_msg)
  | BW_Compl -> failwith "TODO cn_to_ail_unop: Translation not implemented"
  | BW_CLZ_NoSMT | BW_CTZ_NoSMT | BW_FFS_NoSMT ->
    failwith "Failure: Trying to translate SMT-only unop from C source"


(* TODO: Finish *)
let cn_to_ail_binop_internal bt1 bt2 =
  let get_cn_int_type_str bt1 bt2 =
    match (bt1, bt2) with
    | BT.Loc (), BT.Integer | BT.Loc (), BT.Bits _ -> "cn_pointer"
    | BT.Integer, BT.Integer -> "cn_integer"
    | _, BT.Bits (sign, size) | BT.Bits (sign, size), _ ->
      "cn_bits_" ^ str_of_bt_bitvector_type sign size
    | _, _ ->
      let bt1_str = CF.Pp_utils.to_plain_pretty_string (BT.pp bt1) in
      let bt2_str = CF.Pp_utils.to_plain_pretty_string (BT.pp bt2) in
      failwith ("Incompatible CN integer types: " ^ bt1_str ^ " with " ^ bt2_str)
  in
  function
  | IT.And -> (A.And, Some "cn_bool_and")
  | Or -> (A.Or, Some "cn_bool_or")
  (* | Impl *)
  | Add ->
    let bt2_str =
      if BT.equal bt1 BT.(Loc ()) then (
        match bt2 with
        | BT.Integer -> "_cn_integer"
        | BT.Bits (sign, size) -> "_cn_bits_" ^ str_of_bt_bitvector_type sign size
        | _ -> "")
      else
        ""
    in
    (A.(Arithmetic Add), Some (get_cn_int_type_str bt1 bt2 ^ "_add" ^ bt2_str))
  | Sub -> (A.(Arithmetic Sub), Some (get_cn_int_type_str bt1 bt2 ^ "_sub"))
  | Mul | MulNoSMT ->
    (A.(Arithmetic Mul), Some (get_cn_int_type_str bt1 bt2 ^ "_multiply"))
  | Div | DivNoSMT -> (A.(Arithmetic Div), Some (get_cn_int_type_str bt1 bt2 ^ "_divide"))
  | Exp | ExpNoSMT -> (A.And, Some (get_cn_int_type_str bt1 bt2 ^ "_pow"))
  | Rem | RemNoSMT -> (A.(Arithmetic Mod), Some (get_cn_int_type_str bt1 bt2 ^ "_rem"))
  | Mod | ModNoSMT -> (A.(Arithmetic Mod), Some (get_cn_int_type_str bt1 bt2 ^ "_mod"))
  | BW_Xor -> (A.(Arithmetic Bxor), Some (get_cn_int_type_str bt1 bt2 ^ "_xor"))
  | BW_And -> (A.(Arithmetic Band), Some (get_cn_int_type_str bt1 bt2 ^ "_bwand"))
  | BW_Or -> (A.(Arithmetic Bor), Some (get_cn_int_type_str bt1 bt2 ^ "_bwor"))
  | ShiftLeft -> (A.(Arithmetic Shl), Some (get_cn_int_type_str bt1 bt2 ^ "_shift_left"))
  | ShiftRight -> (A.(Arithmetic Shr), Some (get_cn_int_type_str bt1 bt2 ^ "_shift_right"))
  | LT -> (A.Lt, Some (get_cn_int_type_str bt1 bt2 ^ "_lt"))
  | LE -> (A.Le, Some (get_cn_int_type_str bt1 bt2 ^ "_le"))
  | Min -> (A.And, Some (get_cn_int_type_str bt1 bt2 ^ "_min"))
  | Max -> (A.And, Some (get_cn_int_type_str bt1 bt2 ^ "_max"))
  | EQ -> (A.Eq, Some "eq") (* placeholder - equality dealt with in a special way *)
  (* let fn_str = match get_typedef_string (bt_to_ail_ctype bt1) with
     | Some str -> Some (str ^ "_equality")
     | None -> None
     in
     (A.Eq, fn_str) *)
  (* | _ -> failwith "TODO cn_to_ail_binop: Translation not implemented" *)
  | LTPointer -> (A.And, Some "cn_pointer_lt")
  | LEPointer -> (A.And, Some "cn_pointer_le")
  | SetUnion -> failwith "TODO cn_to_ail_binop: SetUnion"
  | SetIntersection -> failwith "TODO cn_to_ail_binop: SetIntersection"
  | SetDifference -> failwith "TODO cn_to_ail_binop: SetDifference"
  | SetMember -> failwith "TODO cn_to_ail_binop: SetMember"
  | Subset -> failwith "TODO cn_to_ail_binop: Subset"
  | Implies -> (A.Or, Some "cn_bool_implies")


(* Assume a specific shape, where sym appears on the RHS (i.e. in e2) *)

let get_underscored_typedef_string_from_bt ?(is_record = false) bt =
  let typedef_name = get_typedef_string (bt_to_ail_ctype bt) in
  match typedef_name with
  | Some str ->
    let str = String.concat "_" (String.split_on_char ' ' str) in
    Some str
  | None ->
    (match bt with
     | BT.Datatype sym ->
       let cn_sym = generate_sym_with_suffix ~suffix:"" sym in
       Some ("struct_" ^ Sym.pp_string cn_sym)
     | BT.Struct sym ->
       let suffix = if is_record then "" else "_cn" in
       let cn_sym = generate_sym_with_suffix ~suffix sym in
       Some ("struct_" ^ Sym.pp_string cn_sym)
     | _ -> None)


let get_type_underscored_str (bt : BT.t) : string option =
  let typedef_name = get_typedef_string (bt_to_ail_ctype bt) in
  match typedef_name with
  | Some str -> Some (String.concat "_" (String.split_on_char ' ' str))
  | None ->
    (match bt with
     | BT.Struct sym ->
       Some ("struct_" ^ Sym.pp_string (generate_sym_with_suffix ~suffix:"_cn" sym))
     | _ -> None)


let get_conversion_to_fn_str (bt : BT.t) : string option =
  let open Option in
  let@ ty_str = get_type_underscored_str bt in
  return ("convert_to_" ^ ty_str)


let get_conversion_from_fn_str (bt : BT.t) : string option =
  let open Option in
  let@ ty_str = get_type_underscored_str bt in
  return ("convert_from_" ^ ty_str)


let wrap_with_convert_to ?sct ail_expr_ bt =
  let conversion_fn_str_opt = get_conversion_to_fn_str bt in
  match conversion_fn_str_opt with
  | Some conversion_fn_str ->
    let args =
      match bt with
      | BT.Map (_bt1, bt2) ->
        let cntype_conversion_fn_str_opt = get_conversion_to_fn_str bt2 in
        let cntype_conversion_fn_str =
          match cntype_conversion_fn_str_opt with
          | Some str -> str
          | None -> failwith "No conversion function for map values"
        in
        let num_elements' =
          match sct with
          | Some (Sctypes.Array (_, Some num_elements)) -> num_elements
          | _ -> failwith "Need number of array elements to create CN map"
        in
        let converted_num_elements =
          A.(
            AilEconst
              (ConstantInteger (IConstant (Z.of_int num_elements', Decimal, None))))
        in
        A.
          [ ail_expr_;
            AilEident (Sym.fresh_pretty cntype_conversion_fn_str);
            converted_num_elements
          ]
      | _ -> [ ail_expr_ ]
    in
    A.(
      AilEcall
        (mk_expr (AilEident (Sym.fresh_pretty conversion_fn_str)), List.map mk_expr args))
  | None -> ail_expr_


let wrap_with_convert_from ?sct ail_expr_ bt =
  let conversion_fn_str_opt = get_conversion_from_fn_str bt in
  match conversion_fn_str_opt with
  | Some conversion_fn_str ->
    let args =
      match bt with
      | BT.Map (_bt1, bt2) ->
        let cntype_conversion_fn_str_opt = get_conversion_from_fn_str bt2 in
        let cntype_conversion_fn_str =
          match cntype_conversion_fn_str_opt with
          | Some str -> str
          | None -> failwith "No conversion function for map values"
        in
        let num_elements' =
          match sct with
          | Some (Sctypes.Array (_, Some num_elements)) -> num_elements
          | _ -> failwith "Need number of array elements to create CN map"
        in
        let converted_num_elements =
          A.(
            AilEconst
              (ConstantInteger (IConstant (Z.of_int num_elements', Decimal, None))))
        in
        A.
          [ ail_expr_;
            AilEident (Sym.fresh_pretty cntype_conversion_fn_str);
            converted_num_elements
          ]
      | _ -> [ ail_expr_ ]
    in
    A.(
      AilEcall
        (mk_expr (AilEident (Sym.fresh_pretty conversion_fn_str)), List.map mk_expr args))
  | None -> ail_expr_


let get_equality_fn_call bt e1 e2 _dts =
  match bt with
  (* TODO (RB) Check if buggy: https://github.com/rems-project/cerberus/pull/652 *)
  | BT.Map (_, val_bt) ->
    let val_ctype_with_ptr = bt_to_ail_ctype val_bt in
    let val_ctype = get_ctype_without_ptr val_ctype_with_ptr in
    let val_str = str_of_ctype val_ctype in
    let val_str = String.concat "_" (String.split_on_char ' ' val_str) in
    let val_equality_str = val_str ^ "_equality" in
    A.(
      AilEcall
        ( mk_expr (AilEident (Sym.fresh_pretty "cn_map_equality")),
          [ e1; e2; mk_expr (AilEident (Sym.fresh_pretty val_equality_str)) ] ))
  | _ ->
    let ctype = bt_to_ail_ctype bt in
    (match get_typedef_string ctype with
     | Some str ->
       (* Printf.printf "typedef string when producing equality function: %s\n" str; *)
       let fn_name = str ^ "_equality" in
       A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [ e1; e2 ]))
     | None ->
       (match rm_ctype ctype with
        | C.(Pointer (_, Ctype (_, Struct sym))) ->
          let prefix = "struct_" in
          let str =
            prefix ^ String.concat "_" (String.split_on_char ' ' (Sym.pp_string sym))
          in
          let fn_name = str ^ "_equality" in
          A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [ e1; e2 ]))
        | _ ->
          failwith
            (Printf.sprintf
               "Could not construct equality function for type %s"
               (CF.Pp_utils.to_plain_pretty_string (BT.pp bt)))))


let rearrange_start_inequality sym (IT.(IT (_, _, loc)) as e1) e2 =
  match IT.term e2 with
  | IT.Binop (binop, (IT.IT (Sym sym1, _, _) as expr1), (IT.IT (Sym sym2, _, _) as expr2))
    ->
    if Sym.equal sym sym1 then (
      let inverse_binop =
        match binop with
        | Add -> IT.Sub
        | Sub -> Add
        | _ -> failwith "Other binops not supported"
      in
      IT.(Binop (inverse_binop, e1, expr2)))
    else if Sym.equal sym sym2 then (
      match binop with
      | Add -> IT.Binop (Sub, e1, expr1)
      | Sub -> failwith "Minus not supported"
      | _ -> failwith "Other binops not supported")
    else
      failwith "Not of correct form"
  | _ ->
    failwith ("TODO rearrange_start_inequality at " ^ Cerb_location.simple_location loc)


let generate_start_expr start_cond sym =
  let start_expr, binop =
    match IT.term start_cond with
    | IT.(Binop (binop, expr1, IT.IT (Sym sym', _, _))) ->
      if Sym.equal sym sym' then
        (expr1, binop)
      else
        failwith "Not of correct form (unlikely case - i's not matching)"
    | IT.(Binop (binop, expr1, expr2)) ->
      ( IT.IT
          (rearrange_start_inequality sym expr1 expr2, BT.Integer, Cerb_location.unknown),
        binop )
    | _ -> failwith "Not of correct form: more complicated RHS of binexpr than just i"
  in
  match binop with
  | LE -> start_expr
  | LT ->
    let one =
      IT.(IT (Const (IT.Z (Z.of_int 1)), IT.bt start_expr, Cerb_location.unknown))
    in
    IT.(IT (Binop (Add, start_expr, one), IT.bt start_expr, Cerb_location.unknown))
  | _ -> failwith "Not of correct form: not Le or Lt"


let rec get_leftmost_of_and_expr = function
  | IT.IT (IT.(Binop (And, lhs, _rhs)), _, _) -> get_leftmost_of_and_expr lhs
  | lhs -> lhs


let rec get_rest_of_expr_r_aux it =
  match IT.term it with
  | IT.(Binop (And, lhs, rhs)) ->
    let r = get_rest_of_expr_r_aux lhs in
    (match IT.term r with
     | Const (Bool true) -> rhs
     | _ -> IT.IT (IT.(Binop (And, r, rhs)), BT.Bool, IT.loc it))
  | _lhs -> IT.IT (Const (Bool true), BT.Bool, IT.loc it)


let get_rest_of_expr_r it =
  match IT.term it with
  | IT.(Binop (And, lhs, rhs)) ->
    let is_simple =
      match (IT.term lhs, IT.term rhs) with
      | Binop (And, _, _), _ | _, Binop (And, _, _) -> false
      | _, _ -> true
    in
    if is_simple then rhs else get_rest_of_expr_r_aux it
  | _ -> IT.IT (Const (Bool true), BT.Bool, IT.loc it)


let convert_from_cn_bool_sym =
  Sym.fresh_named (Option.get (get_conversion_from_fn_str BT.Bool))


let wrap_with_convert_from_cn_bool expr =
  let (A.AnnotatedExpression (_, _, _, expr_)) = expr in
  mk_expr (wrap_with_convert_from expr_ BT.Bool)


let cn_bool_true_expr : CF.GenTypes.genTypeCategory A.expression =
  mk_expr (wrap_with_convert_to true_const BT.Bool)


let gen_bool_while_loop sym bt start_expr while_cond ?(if_cond_opt = None) (bs, ss, e) =
  (*
     Input:
     each (bt sym; start_expr <= sym && while_cond) {t}

     where (bs, ss, e) = cn_internal_to_ail called on t with PassBack
  *)
  let b = Sym.fresh () in
  let b_ident = A.(AilEident b) in
  let b_binding = create_binding b (bt_to_ail_ctype BT.Bool) in
  let b_decl = A.(AilSdeclaration [ (b, Some cn_bool_true_expr) ]) in
  let incr_var = A.(AilEident sym) in
  let incr_var_binding = create_binding sym (bt_to_ail_ctype bt) in
  let start_decl = A.(AilSdeclaration [ (sym, Some (mk_expr start_expr)) ]) in
  let typedef_name = get_typedef_string (bt_to_ail_ctype bt) in
  let incr_func_name =
    match typedef_name with Some str -> str ^ "_increment" | None -> ""
  in
  let cn_bool_and_sym = Sym.fresh_pretty "cn_bool_and" in
  let rhs_and_expr_ =
    A.(AilEcall (mk_expr (AilEident cn_bool_and_sym), [ mk_expr b_ident; e ]))
  in
  let b_assign =
    A.(AilSexpr (mk_expr (AilEassign (mk_expr b_ident, mk_expr rhs_and_expr_))))
  in
  (* let incr_stat = A.(AilSexpr (mk_expr (AilEunary (PostfixIncr, mk_expr incr_var)))) in *)
  let incr_stat =
    A.(
      AilSexpr
        (mk_expr
           (AilEcall
              (mk_expr (AilEident (Sym.fresh_pretty incr_func_name)), [ mk_expr incr_var ]))))
  in
  let while_cond_with_conversion = wrap_with_convert_from_cn_bool while_cond in
  let loop_body =
    match if_cond_opt with
    | Some if_cond_expr ->
      List.map
        mk_stmt
        [ A.(
            AilSif
              ( wrap_with_convert_from_cn_bool if_cond_expr,
                mk_stmt (AilSblock ([], List.map mk_stmt (ss @ [ b_assign; incr_stat ]))),
                mk_stmt (AilSblock ([], [ mk_stmt AilSskip ])) ));
          incr_stat
        ]
    | None -> List.map mk_stmt (ss @ [ b_assign; incr_stat ])
  in
  let while_loop =
    A.(AilSwhile (while_cond_with_conversion, mk_stmt (AilSblock (bs, loop_body)), 0))
  in
  let block =
    A.(AilSblock ([ incr_var_binding ], List.map mk_stmt [ start_decl; while_loop ]))
  in
  ([ b_binding ], [ b_decl; block ], mk_expr b_ident)


let rec cn_to_ail_const_internal const =
  let ail_const =
    match const with
    | IT.Z z -> A.AilEconst (ConstantInteger (IConstant (z, Decimal, None)))
    | MemByte { alloc_id = _; value = i } | Bits (_, i) ->
      A.AilEconst (ConstantInteger (IConstant (i, Decimal, None)))
    | Q q -> A.AilEconst (ConstantFloating (Q.to_string q, None))
    | Pointer z ->
      (* Printf.printf "In Pointer case; const\n"; *)
      let ail_const', _ = cn_to_ail_const_internal (IT.Z z.addr) in
      A.AilEunary (Address, mk_expr ail_const')
    | Alloc_id _ -> failwith "TODO Alloc_id"
    | Bool b ->
      A.AilEconst (ConstantPredefined (if b then PConstantTrue else PConstantFalse))
    | Unit -> A.AilEconst ConstantNull (* Gets overridden by dest_with_unit_check *)
    | Null -> A.AilEconst ConstantNull
    | CType_const _ -> failwith "TODO CType_const"
    | Default _bt -> failwith "TODO Default"
  in
  let is_unit = const == Unit in
  (ail_const, is_unit)


type ail_bindings_and_statements =
  A.bindings * CF.GenTypes.genTypeCategory A.statement_ list

type ail_executable_spec =
  { pre : ail_bindings_and_statements;
    post : ail_bindings_and_statements;
    in_stmt : (Locations.t * ail_bindings_and_statements) list
  }

let empty_ail_executable_spec = { pre = ([], []); post = ([], []); in_stmt = [] }

type 'a dest =
  | Assert : Cerb_location.t -> ail_bindings_and_statements dest
  | Return : ail_bindings_and_statements dest
  | AssignVar : C.union_tag -> ail_bindings_and_statements dest
  | PassBack
      : (A.bindings
        * CF.GenTypes.genTypeCategory A.statement_ list
        * CF.GenTypes.genTypeCategory A.expression)
          dest

(* bool flag for checking if expression is unit - needs special treatment *)
let dest_with_unit_check
  : type a.
    a dest ->
    A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
    * bool ->
    a
  =
  fun d (b, s, e, is_unit) ->
  match d with
  | Assert loc ->
    let assert_stmts = generate_cn_assert ~cn_source_loc_opt:(Some loc) e in
    (b, s @ assert_stmts)
  | Return ->
    let return_stmt = if is_unit then A.(AilSreturnVoid) else A.(AilSreturn e) in
    (b, s @ [ return_stmt ])
  | AssignVar x ->
    let assign_stmt = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident x), e)))) in
    (b, s @ [ assign_stmt ])
  | PassBack -> (b, s, e)


let dest
  : type a.
    a dest ->
    A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression ->
    a
  =
  fun d (b, s, e) -> dest_with_unit_check d (b, s, e, false)


let prefix
  : type a. a dest -> A.bindings * CF.GenTypes.genTypeCategory A.statement_ list -> a -> a
  =
  fun d (b1, s1) u ->
  match (d, u) with
  | Assert _, (b2, s2) -> (b1 @ b2, s1 @ s2)
  | Return, (b2, s2) -> (b1 @ b2, s1 @ s2)
  | AssignVar _, (b2, s2) -> (b1 @ b2, s1 @ s2)
  | PassBack, (b2, s2, e) -> (b1 @ b2, s1 @ s2, e)


let empty_for_dest : type a. a dest -> a =
  fun d ->
  match d with
  | Assert _ -> ([], [])
  | Return -> ([], [])
  | AssignVar _ -> ([], [])
  | PassBack -> ([], [], mk_expr empty_ail_expr)


let generate_ownership_function ~with_ownership_checking ctype
  : A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition
  =
  let ctype_str = str_of_ctype ctype in
  (* Printf.printf ("ctype_str: %s\n") ctype_str; *)
  let ctype_str = String.concat "_" (String.split_on_char ' ' ctype_str) in
  let fn_sym = Sym.fresh_pretty ("owned_" ^ ctype_str) in
  let param1_sym = Sym.fresh_pretty "cn_ptr" in
  let cast_expr =
    mk_expr
      A.(
        AilEcast
          ( empty_qualifiers,
            mk_ctype C.(Pointer (empty_qualifiers, ctype)),
            mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), Id.id "ptr")) ))
  in
  let generic_c_ptr_sym = Sym.fresh_pretty "generic_c_ptr" in
  let generic_c_ptr_bs, generic_c_ptr_ss =
    if with_ownership_checking then (
      let uintptr_t_type = C.uintptr_t in
      let generic_c_ptr_binding = create_binding generic_c_ptr_sym uintptr_t_type in
      let uintptr_t_cast_expr =
        mk_expr A.(AilEcast (empty_qualifiers, uintptr_t_type, cast_expr))
      in
      let generic_c_ptr_assign_stat_ =
        A.(AilSdeclaration [ (generic_c_ptr_sym, Some uintptr_t_cast_expr) ])
      in
      ([ generic_c_ptr_binding ], [ generic_c_ptr_assign_stat_ ]))
    else
      ([], [])
  in
  let param2_sym = Sym.fresh_pretty "owned_enum" in
  let param1 = (param1_sym, bt_to_ail_ctype BT.(Loc ())) in
  let param2 =
    (param2_sym, mk_ctype C.(Basic (Integer (Enum (Sym.fresh_pretty "OWNERSHIP")))))
  in
  let param_syms, param_types = List.split [ param1; param2 ] in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  let ownership_fcall_maybe =
    if with_ownership_checking then (
      let ownership_fn_sym = Sym.fresh_pretty "cn_check_ownership" in
      let ownership_fn_args =
        A.
          [ AilEident param2_sym;
            AilEident generic_c_ptr_sym;
            AilEsizeof (empty_qualifiers, ctype)
          ]
      in
      [ A.(
          AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident ownership_fn_sym),
                    List.map mk_expr ownership_fn_args ))))
      ])
    else
      []
  in
  let deref_expr_ = A.(AilEunary (Indirection, cast_expr)) in
  let sct_opt = Sctypes.of_ctype ctype in
  let sct =
    match sct_opt with
    | Some sct -> sct
    | None -> failwith "Bad sctype when trying to generate ownership function"
  in
  let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
  let ret_type = bt_to_ail_ctype bt in
  let return_stmt = A.(AilSreturn (mk_expr (wrap_with_convert_to ~sct deref_expr_ bt))) in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( Cerb_location.unknown,
        empty_attributes,
        A.(
          Decl_function
            (false, (empty_qualifiers, ret_type), param_types, false, false, false)) ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( Cerb_location.unknown,
        0,
        empty_attributes,
        param_syms,
        mk_stmt
          A.(
            AilSblock
              ( generic_c_ptr_bs,
                List.map
                  mk_stmt
                  (generic_c_ptr_ss @ ownership_fcall_maybe @ [ return_stmt ]) )) ) )
  in
  (decl, def)


let mk_alloc_expr (ct_ : C.ctype_) : CF.GenTypes.genTypeCategory A.expression =
  A.(
    mk_expr
      (AilEcast
         ( C.no_qualifiers,
           C.(mk_ctype_pointer no_qualifiers (mk_ctype ct_)),
           mk_expr
             (AilEcall
                ( mk_expr (AilEident (Sym.fresh_pretty "alloc")),
                  [ mk_expr (AilEsizeof (empty_qualifiers, mk_ctype ct_)) ] )) )))


let is_sym_obj_address sym =
  match Sym.symbol_description sym with SD_ObjectAddress _ -> true | _ -> false


(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
(* TODO: Use mu_datatypes from Mucore program instead of cn_datatypes *)
let rec cn_to_ail_expr_aux_internal
  : type a.
    _ option ->
    _ option ->
    _ CF.Cn.cn_datatype list ->
    (C.union_tag * C.ctype) list ->
    IT.t ->
    a dest ->
    a
  =
  fun const_prop pred_name dts globals (IT (term_, basetype, loc)) d ->
  match term_ with
  | Const const ->
    let ail_expr_, is_unit = cn_to_ail_const_internal const in
    dest_with_unit_check
      d
      ([], [], mk_expr (wrap_with_convert_to ail_expr_ basetype), is_unit)
  | Sym sym ->
    let sym =
      if String.equal (Sym.pp_string sym) "return" then
        Sym.fresh_pretty "return_cn"
      else
        sym
    in
    let ail_expr_ =
      match const_prop with
      | Some (sym2, cn_const) ->
        if CF.Symbol.equal_sym sym sym2 then (
          let ail_const, _ = cn_to_ail_const_internal cn_const in
          ail_const)
        else
          A.(AilEident sym)
      | None -> A.(AilEident sym)
      (* TODO: Check. Need to do more work if this is only a CN var *)
    in
    let ail_expr_ =
      if is_sym_obj_address sym then
        wrap_with_convert_to A.(AilEunary (Address, mk_expr ail_expr_)) basetype
      else
        ail_expr_
    in
    dest d ([], [], mk_expr ail_expr_)
  | Binop (bop, t1, t2) ->
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack
    in
    let b2, s2, e2 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t2 PassBack
    in
    let ail_bop, annot = cn_to_ail_binop_internal (IT.basetype t1) (IT.basetype t2) bop in
    let str =
      match annot with Some str -> str | None -> failwith "No CN binop function found"
    in
    let default_ail_binop =
      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty str)), [ e1; e2 ]))
    in
    (*
       let is_map it =
       match IT.bt it with
       | BT.Map (bt1, bt2) ->
       Printf.printf "Type of %s: Map(%s, %s)\n" (str_of_it_ (IT.term it)) (str_of_ctype (bt_to_ail_ctype bt1)) (str_of_ctype (bt_to_ail_ctype bt2));
       true
       | _ -> false
       in *)
    let ail_expr_ =
      match ail_bop with
      | Eq -> get_equality_fn_call (IT.bt t1) e1 e2 dts
      | _ -> default_ail_binop
    in
    dest d (b1 @ b2, s1 @ s2, mk_expr ail_expr_)
  | Unop (unop, t) ->
    let b, s, e =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack
    in
    let _ail_unop, annot = cn_to_ail_unop_internal (IT.bt t) unop in
    let str =
      match annot with Some str -> str | None -> failwith "No CN unop function found"
    in
    let ail_expr_ = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty str)), [ e ])) in
    dest d (b, s, mk_expr ail_expr_)
  | SizeOf sct ->
    let ail_expr_ = A.(AilEsizeof (empty_qualifiers, Sctypes.to_ctype sct)) in
    let ail_call_ = wrap_with_convert_to ~sct ail_expr_ basetype in
    dest d ([], [], mk_expr ail_call_)
  | OffsetOf _ -> failwith "TODO OffsetOf"
  | ITE (t1, t2, t3) ->
    let result_sym = Sym.fresh () in
    let result_ident = A.(AilEident result_sym) in
    let result_binding = create_binding result_sym (bt_to_ail_ctype (IT.bt t2)) in
    let result_decl = A.(AilSdeclaration [ (result_sym, None) ]) in
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack
    in
    let wrapped_cond =
      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "convert_from_cn_bool")), [ e1 ]))
    in
    let b2, s2 =
      cn_to_ail_expr_aux_internal
        const_prop
        pred_name
        dts
        globals
        t2
        (AssignVar result_sym)
    in
    let b3, s3 =
      cn_to_ail_expr_aux_internal
        const_prop
        pred_name
        dts
        globals
        t3
        (AssignVar result_sym)
    in
    let ite_stat =
      A.(
        AilSif
          ( mk_expr wrapped_cond,
            mk_stmt (AilSblock (b2, List.map mk_stmt s2)),
            mk_stmt (AilSblock (b3, List.map mk_stmt s3)) ))
    in
    dest d (result_binding :: b1, (result_decl :: s1) @ [ ite_stat ], mk_expr result_ident)
  | EachI ((r_start, (sym, bt'), r_end), t) ->
    (*
       Input:

    each (bt sym; r_start <= sym && sym < r_end) {t} 
        
    , where t contains sym *)

    (*
       Want to translate to:
    bool b = true; // b should be a fresh sym each time

    {
      signed int sym = r_start;
      while (sym < r_end) {
        b = b && t;
        sym++;
      }   
    }
    
    assign/return/assert/passback b
    *)
    let mk_int_const n = IT.(IT (Const (Z (Z.of_int n)), bt', Cerb_location.unknown)) in
    let start_const_it = mk_int_const r_start in
    let end_const_it = mk_int_const r_end in
    let incr_var = IT.(IT (Sym sym, bt', Cerb_location.unknown)) in
    let _, _, start_int_const =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals start_const_it PassBack
    in
    let while_cond_it =
      IT.(IT (Binop (LT, incr_var, end_const_it), bt', Cerb_location.unknown))
    in
    let _, _, while_cond =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals while_cond_it PassBack
    in
    let translated_t =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack
    in
    let bs, ss, e =
      gen_bool_while_loop sym bt' (rm_expr start_int_const) while_cond translated_t
    in
    dest d (bs, ss, e)
  (* add Z3's Distinct for separation facts *)
  | Tuple _ts -> failwith "TODO1"
  | NthTuple (_i, _t) -> failwith "TODO2"
  | Struct (tag, ms) ->
    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in
    let cn_struct_tag = generate_sym_with_suffix ~suffix:"_cn" tag in
    let generate_ail_stat (id, it) =
      let b, s, e =
        cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack
      in
      let ail_memberof = A.(AilEmemberofptr (mk_expr res_ident, id)) in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (mk_expr ail_memberof, e)))) in
      (b, s, assign_stat)
    in
    let ctype_ = C.(Pointer (empty_qualifiers, mk_ctype (Struct cn_struct_tag))) in
    let res_binding = create_binding res_sym (mk_ctype ctype_) in
    let fn_call = mk_alloc_expr (Struct cn_struct_tag) in
    let alloc_stat = A.(AilSdeclaration [ (res_sym, Some fn_call) ]) in
    let b, s = ([ res_binding ], [ alloc_stat ]) in
    let bs, ss, assign_stats = list_split_three (List.map generate_ail_stat ms) in
    dest d (List.concat bs @ b, List.concat ss @ s @ assign_stats, mk_expr res_ident)
  | RecordMember (t, m) ->
    (* Currently assuming records only exist *)
    let b, s, e =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack
    in
    (* let ail_expr_ = match pred_name with
       | Some sym -> A.(AilEmemberofptr (e, m))
       | None -> A.(AilEmemberofptr (e, m))
       in *)
    dest d (b, s, mk_expr A.(AilEmemberofptr (e, m)))
  | StructMember (t, m) ->
    let b, s, e =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack
    in
    let ail_expr_ = A.(AilEmemberofptr (e, m)) in
    dest d (b, s, mk_expr ail_expr_)
  | StructUpdate ((struct_term, m), new_val) ->
    let struct_tag =
      match IT.bt struct_term with
      | BT.Struct tag -> tag
      | _ -> failwith "Cannot do StructUpdate on non-struct term"
    in
    let tag_defs = Pmap.bindings_list (CF.Tags.tagDefs ()) in
    let matching_tag_defs =
      List.filter (fun (sym, (_, __def)) -> Sym.equal struct_tag sym) tag_defs
    in
    let _, (_, tag_def) =
      if List.is_empty matching_tag_defs then
        failwith "Struct not found in tagDefs"
      else
        List.nth matching_tag_defs 0
    in
    (match tag_def with
     | C.StructDef (members, _) ->
       let b1, s1, e1 =
         cn_to_ail_expr_aux_internal const_prop pred_name dts globals struct_term PassBack
       in
       let b2, s2, e2 =
         cn_to_ail_expr_aux_internal const_prop pred_name dts globals new_val PassBack
       in
       let res_sym = Sym.fresh () in
       let res_ident = mk_expr A.(AilEident res_sym) in
       let cn_struct_tag = generate_sym_with_suffix ~suffix:"_cn" struct_tag in
       let res_binding =
         create_binding
           res_sym
           C.(mk_ctype_pointer empty_qualifiers (mk_ctype (Struct cn_struct_tag)))
       in
       let alloc_call = mk_alloc_expr (Struct cn_struct_tag) in
       let res_decl = A.(AilSdeclaration [ (res_sym, Some alloc_call) ]) in
       let generate_member_assignment m (member_id, _) =
         let lhs_memberof_expr_ = mk_expr A.(AilEmemberofptr (res_ident, member_id)) in
         let rhs =
           if Id.equal member_id m then
             e2
           else
             mk_expr (AilEmemberofptr (e1, member_id))
         in
         A.(AilSexpr (mk_expr (AilEassign (lhs_memberof_expr_, rhs))))
       in
       let member_assignments = List.map (generate_member_assignment m) members in
       dest
         d
         (b1 @ b2 @ [ res_binding ], s1 @ s2 @ (res_decl :: member_assignments), res_ident)
     | UnionDef _ -> failwith "Can't apply StructUpdate to a C union")
    (* Allocation *)
  | Record ms ->
    (* Could either be (1) standalone record or (2) part of datatype. Case (2) may not exist soon *)
    (* Might need to pass records around like datatypes *)
    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in
    let generate_ail_stat (id, it) =
      let b, s, e =
        cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack
      in
      let ail_memberof = A.(AilEmemberofptr (mk_expr res_ident, id)) in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (mk_expr ail_memberof, e)))) in
      (b, s, assign_stat)
    in
    let transformed_ms =
      List.map (fun (id, it) -> (id, bt_to_cn_base_type (IT.bt it))) ms
    in
    let sym_name = lookup_records_map transformed_ms in
    let ctype_ = C.(Pointer (empty_qualifiers, mk_ctype (Struct sym_name))) in
    let res_binding = create_binding res_sym (mk_ctype ctype_) in
    let fn_call = mk_alloc_expr (Struct sym_name) in
    let alloc_stat = A.(AilSdeclaration [ (res_sym, Some fn_call) ]) in
    let b, s = ([ res_binding ], [ alloc_stat ]) in
    let bs, ss, assign_stats = list_split_three (List.map generate_ail_stat ms) in
    dest d (List.concat bs @ b, List.concat ss @ s @ assign_stats, mk_expr res_ident)
  | RecordUpdate ((_t1, _m), _t2) -> failwith "TODO6"
  (* Allocation *)
  | Constructor (sym, ms) ->
    let rec find_dt_from_constructor constr_sym dts =
      match dts with
      | [] -> failwith "Datatype not found" (* Not found *)
      | dt :: dts' ->
        let matching_cases =
          List.filter (fun (c_sym, _members) -> Sym.equal c_sym constr_sym) dt.cn_dt_cases
        in
        if List.length matching_cases != 0 then (
          let _, members = List.hd matching_cases in
          (dt, members))
        else
          find_dt_from_constructor constr_sym dts'
    in
    let parent_dt, _members = find_dt_from_constructor sym dts in
    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in
    let ctype_ = C.(Pointer (empty_qualifiers, mk_ctype (Struct parent_dt.cn_dt_name))) in
    let res_binding = create_binding res_sym (mk_ctype ctype_) in
    let alloc_sym = Sym.fresh_pretty "alloc" in
    let fn_call =
      A.(
        AilEcast
          ( C.no_qualifiers,
            C.(mk_ctype_pointer no_qualifiers (mk_ctype (Struct parent_dt.cn_dt_name))),
            mk_expr
              (AilEcall
                 ( mk_expr (AilEident alloc_sym),
                   [ mk_expr
                       (AilEsizeof
                          (empty_qualifiers, mk_ctype C.(Struct parent_dt.cn_dt_name)))
                   ] )) ))
    in
    let ail_decl = A.(AilSdeclaration [ (res_sym, Some (mk_expr fn_call)) ]) in
    let lc_constr_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true sym in
    let e_ = A.(AilEmemberofptr (mk_expr res_ident, Id.id "u")) in
    let e_' = A.(AilEmemberof (mk_expr e_, create_id_from_sym lc_constr_sym)) in
    let generate_ail_stat (id, it) =
      let b, s, e =
        cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack
      in
      let ail_memberof =
        if Id.equal id (Id.id "tag") then
          e
        else (
          let e_'' = A.(AilEmemberofptr (mk_expr e_', id)) in
          mk_expr e_'')
      in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (ail_memberof, e)))) in
      (b, s, assign_stat)
    in
    let constr_alloc_call =
      A.(
        AilEcast
          ( C.no_qualifiers,
            C.(mk_ctype_pointer no_qualifiers (mk_ctype (Struct lc_constr_sym))),
            mk_expr
              (AilEcall
                 ( mk_expr (AilEident alloc_sym),
                   [ mk_expr
                       (AilEsizeof (empty_qualifiers, mk_ctype C.(Struct lc_constr_sym)))
                   ] )) ))
    in
    let constr_allocation_stat =
      if List.is_empty ms then
        []
      else
        [ A.(AilSexpr (mk_expr (AilEassign (mk_expr e_', mk_expr constr_alloc_call)))) ]
    in
    let bs, ss, assign_stats = list_split_three (List.map generate_ail_stat ms) in
    let uc_constr_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true sym in
    let tag_member_ptr = A.(AilEmemberofptr (mk_expr res_ident, Id.id "tag")) in
    let tag_assign =
      A.(
        AilSexpr
          (mk_expr
             (AilEassign (mk_expr tag_member_ptr, mk_expr (AilEident uc_constr_sym)))))
    in
    dest
      d
      ( List.concat bs @ [ res_binding ],
        [ ail_decl; tag_assign ] @ List.concat ss @ constr_allocation_stat @ assign_stats,
        mk_expr res_ident )
  | MemberShift (it, tag, member) ->
    let membershift_macro_sym = Sym.fresh_pretty "cn_member_shift" in
    let bs, ss, e =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack
    in
    let ail_fcall =
      A.(
        AilEcall
          ( mk_expr (AilEident membershift_macro_sym),
            [ e;
              mk_expr (AilEident tag);
              mk_expr (AilEident (create_sym_from_id member))
            ] ))
    in
    (* let ail_expr_ = A.(AilEoffsetof (C.(Ctype ([], Struct tag)), member)) in *)
    dest d (bs, ss, mk_expr ail_fcall)
  | ArrayShift { base; ct; index } ->
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals base PassBack
    in
    let b2, s2, e2 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals index PassBack
    in
    let sizeof_expr = mk_expr A.(AilEsizeof (empty_qualifiers, Sctypes.to_ctype ct)) in
    let ail_expr_ =
      A.(
        AilEcall
          ( mk_expr (AilEident (Sym.fresh_pretty "cn_array_shift")),
            [ e1; sizeof_expr; e2 ] ))
    in
    dest d (b1 @ b2, s1 @ s2, mk_expr ail_expr_)
  | CopyAllocId _ -> failwith "TODO CopyAllocId"
  | HasAllocId _ -> failwith "TODO HasAllocId"
  | Nil _bt -> failwith "TODO8"
  | Cons (_x, _xs) -> failwith "TODO9"
  | Head xs ->
    let b, s, e =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals xs PassBack
    in
    (* dereference to get first value, where xs is assumed to be a pointer *)
    let ail_expr_ = A.(AilEunary (Indirection, e)) in
    dest d (b, s, mk_expr ail_expr_)
  | Tail _xs -> failwith "TODO11"
  | NthList (_t1, _t2, _t3) -> failwith "TODO12"
  | ArrayToList (_t1, _t2, _t3) -> failwith "TODO13"
  | Representable (_ct, _t) -> failwith "TODO14"
  | Good (_ct, _t) ->
    dest d ([], [], cn_bool_true_expr)
    (* cn_to_ail_expr_aux_internal const_prop pred_name dts globals t d *)
  | Aligned _t_and_align -> failwith "TODO16"
  | WrapI (_ct, t) -> cn_to_ail_expr_aux_internal const_prop pred_name dts globals t d
  | MapConst (_bt, _t) -> failwith "TODO18"
  | MapSet (m, key, value) ->
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals m PassBack
    in
    let key_term =
      if IT.bt key == BT.Integer then
        key
      else
        IT.IT (Cast (BT.Integer, key), BT.Integer, Cerb_location.unknown)
    in
    let b2, s2, e2 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals key_term PassBack
    in
    let b3, s3, e3 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals value PassBack
    in
    let new_map_sym = Sym.fresh () in
    let new_map_binding = create_binding new_map_sym (bt_to_ail_ctype (IT.bt m)) in
    let map_deep_copy_fcall =
      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_map_deep_copy")), [ e1 ]))
    in
    let new_map_decl =
      A.(AilSdeclaration [ (new_map_sym, Some (mk_expr map_deep_copy_fcall)) ])
    in
    let map_set_fcall =
      A.(
        AilEcall
          ( mk_expr (AilEident (Sym.fresh_pretty "cn_map_set")),
            [ mk_expr A.(AilEident new_map_sym); e2; e3 ] ))
    in
    dest
      d
      ( b1 @ b2 @ b3 @ [ new_map_binding ],
        s1 @ s2 @ s3 @ [ new_map_decl ],
        mk_expr map_set_fcall )
  | MapGet (m, key) ->
    (* Only works when index is a cn_integer *)
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals m PassBack
    in
    let key_term =
      if IT.bt key == BT.Integer then
        key
      else
        IT.IT (Cast (BT.Integer, key), BT.Integer, Cerb_location.unknown)
    in
    let b2, s2, e2 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals key_term PassBack
    in
    let is_record = match BT.map_bt (IT.bt m) with _, Record _ -> true | _ -> false in
    let cntype_str_opt = get_underscored_typedef_string_from_bt ~is_record basetype in
    let map_get_str =
      match cntype_str_opt with
      | Some str -> "cn_map_get_" ^ str
      | None -> failwith "could not get cntype string in MapGet"
    in
    let map_get_fcall =
      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty map_get_str)), [ e1; e2 ]))
    in
    let _key_bt, val_bt = BT.map_bt (IT.bt m) in
    let ctype = bt_to_ail_ctype val_bt in
    let cast_expr_ = A.(AilEcast (empty_qualifiers, ctype, mk_expr map_get_fcall)) in
    dest d (b1 @ b2, s1 @ s2, mk_expr cast_expr_)
  | MapDef ((_sym, _bt), _t) -> failwith "TODO21"
  | Apply (sym, ts) ->
    let bs_ss_es =
      List.map
        (fun e -> cn_to_ail_expr_aux_internal const_prop pred_name dts globals e PassBack)
        ts
    in
    let bs, ss, es = list_split_three bs_ss_es in
    let f = mk_expr A.(AilEident sym) in
    let ail_expr_ = A.AilEcall (f, es) in
    let error_msg_update_stats_ =
      generate_error_msg_info_update_stats ~cn_source_loc_opt:(Some loc) ()
    in
    dest d (List.concat bs, List.concat ss @ error_msg_update_stats_, mk_expr ail_expr_)
  | Let ((var, t1), body) ->
    let b1, s1, e1 =
      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack
    in
    let ctype = bt_to_ail_ctype (IT.bt t1) in
    let binding = create_binding var ctype in
    let ail_assign = A.(AilSdeclaration [ (var, Some e1) ]) in
    prefix
      d
      (b1 @ [ binding ], s1 @ [ ail_assign ])
      (cn_to_ail_expr_aux_internal const_prop pred_name dts globals body d)
  | Match (t, ps) ->
    (* PATTERN COMPILER *)
    let mk_pattern pattern_ bt loc = T.(Pat (pattern_, bt, loc)) in
    let simplify_leading_variable t1 (ps, t2) =
      match ps with
      | T.(Pat (PSym sym', p_bt, pt_loc)) :: ps' ->
        ( mk_pattern T.PWild p_bt pt_loc :: ps',
          T.(IT (Let ((sym', t1), t2), IT.basetype t2, pt_loc)) )
      | p :: ps' -> (p :: ps', t2)
      | [] -> assert false
    in
    let leading_wildcard (ps, _) =
      match ps with
      | T.(Pat (PWild, _, _)) :: _ps' -> true
      | _ :: _ps' -> false
      | [] -> failwith "Empty patterns not allowed"
    in
    let expand_datatype c (ps, e) =
      match ps with
      | T.(Pat (PWild, _p_bt, _p_loc) as pat) :: ps' -> Some (pat :: ps', e)
      | T.(Pat (PConstructor (c_nm, members), _, _)) :: ps' ->
        if Sym.equal_sym c c_nm then (
          let member_patterns = List.map snd members in
          Some (member_patterns @ ps', e))
        else
          None
      | _ :: _ -> failwith "Non-sum pattern"
      | [] -> assert false
    in
    let transform_switch_expr e = A.(AilEmemberofptr (e, Id.id "tag")) in
    (* TODO: Incorporate destination passing recursively into this. Might need PassBack throughout, like in cn_to_ail_expr_aux function *)
    (* Matrix algorithm for pattern compilation *)
    let rec translate
      :  int -> IT.t list -> (BT.t IT.pattern list * IT.t) list ->
      A.bindings * _ A.statement_ list
      =
      fun count vars cases ->
      match vars with
      | [] ->
        (match cases with
         | ([], t) :: _rest ->
           let bs, ss =
             match d with
             | Assert loc ->
               cn_to_ail_expr_aux_internal const_prop pred_name dts globals t (Assert loc)
             | Return ->
               cn_to_ail_expr_aux_internal const_prop pred_name dts globals t Return
             | AssignVar x ->
               cn_to_ail_expr_aux_internal
                 const_prop
                 pred_name
                 dts
                 globals
                 t
                 (AssignVar x)
             | PassBack -> failwith "TODO Pattern Match PassBack"
           in
           (bs, ss)
         | [] -> failwith "Incomplete pattern match"
         | (_ :: _, _e) :: _rest -> failwith "Redundant patterns")
      | term :: vs ->
        let cases = List.map (simplify_leading_variable term) cases in
        if List.for_all leading_wildcard cases then (
          let cases = List.map (fun (ps, e) -> (List.tl ps, e)) cases in
          let bindings', stats' = translate count vs cases in
          (bindings', stats'))
        else (
          match IT.bt term with
          | BT.Datatype sym ->
            let cn_dt = List.filter (fun dt -> Sym.equal sym dt.cn_dt_name) dts in
            (match cn_dt with
             | [] -> failwith "Datatype not found"
             | dt :: _ ->
               let b1, s1, e1 =
                 cn_to_ail_expr_aux_internal
                   const_prop
                   pred_name
                   dts
                   globals
                   term
                   PassBack
               in
               let build_case (constr_sym, members_with_types) =
                 let cases' = List.filter_map (expand_datatype constr_sym) cases in
                 let suffix = "_" ^ string_of_int count in
                 let lc_sym =
                   generate_sym_with_suffix ~suffix:"" ~lowercase:true constr_sym
                 in
                 let count_sym =
                   generate_sym_with_suffix ~suffix ~lowercase:true constr_sym
                 in
                 let rhs_memberof_ptr = A.(AilEmemberofptr (e1, Id.id "u")) in
                 (* TODO: Remove hack *)
                 let rhs_memberof =
                   A.(AilEmemberof (mk_expr rhs_memberof_ptr, create_id_from_sym lc_sym))
                 in
                 let constr_binding =
                   create_binding
                     count_sym
                     (mk_ctype C.(Pointer (empty_qualifiers, mk_ctype C.(Struct lc_sym))))
                 in
                 let constructor_var_assign =
                   mk_stmt
                     A.(AilSdeclaration [ (count_sym, Some (mk_expr rhs_memberof)) ])
                 in
                 let ids, ts = List.split (List.rev members_with_types) in
                 let bts = List.map cn_base_type_to_bt ts in
                 let new_constr_it =
                   IT.IT (Sym count_sym, BT.Struct lc_sym, Cerb_location.unknown)
                 in
                 let vars' =
                   List.map (fun id -> T.StructMember (new_constr_it, id)) ids
                 in
                 let terms' =
                   List.map
                     (fun (var', bt') -> T.IT (var', bt', Cerb_location.unknown))
                     (List.combine vars' bts)
                 in
                 let bindings, member_stats =
                   translate (count + 1) (terms' @ vs) cases'
                 in
                 (* TODO: Check *)
                 let stat_block =
                   A.AilSblock
                     ( constr_binding :: bindings,
                       constructor_var_assign :: List.map mk_stmt member_stats )
                 in
                 let tag_sym =
                   generate_sym_with_suffix ~suffix:"" ~uppercase:true constr_sym
                 in
                 let attribute : CF.Annot.attribute =
                   { attr_ns = None;
                     attr_id = create_id_from_sym tag_sym;
                     attr_args = []
                   }
                 in
                 let ail_case =
                   A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt stat_block))
                 in
                 A.(
                   AnnotatedStatement
                     (Cerb_location.unknown, CF.Annot.Attrs [ attribute ], ail_case))
               in
               let e1_transformed = transform_switch_expr e1 in
               let ail_case_stmts = List.map build_case dt.cn_dt_cases in
               let switch =
                 A.(
                   AilSswitch
                     (mk_expr e1_transformed, mk_stmt (AilSblock ([], ail_case_stmts))))
               in
               (b1, s1 @ [ switch ]))
          | _ ->
            (* Cannot have non-variable, non-wildcard pattern besides struct *)
            let bt_string_opt = get_typedef_string (bt_to_ail_ctype (IT.bt term)) in
            let bt_string =
              match bt_string_opt with
              | Some str -> str
              | None -> failwith "no typedef string"
            in
            let err_msg = "Unexpected pattern from term with type " ^ bt_string in
            failwith err_msg)
    in
    let translate_real
      : type a. IT.t list -> (BT.t IT.pattern list * IT.t) list -> a dest -> a
      =
      fun vars cases d ->
      let bs, ss = translate 1 vars cases in
      match d with
      | Assert _ -> (bs, ss)
      | Return -> (bs, ss)
      | AssignVar _x -> failwith "TODO translate_real 1"
      | PassBack -> failwith "TODO translate_real 2"
    in
    let ps' = List.map (fun (p, t) -> ([ p ], t)) ps in
    translate_real [ t ] ps' d
  | Cast (bt, t) ->
    let ail_expr_, b, s =
      match bt with
      | BT.Alloc_id ->
        let ail_const_expr_ =
          A.AilEconst (ConstantInteger (IConstant (Z.of_int 0, Decimal, None)))
        in
        (wrap_with_convert_to ail_const_expr_ BT.Alloc_id, [], [])
      | _ ->
        let b, s, e =
          cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack
        in
        let ail_expr_ =
          match
            ( get_typedef_string (bt_to_ail_ctype bt),
              get_typedef_string (bt_to_ail_ctype (IT.bt t)) )
          with
          | Some cast_type_str, Some original_type_str ->
            let fn_name = "cast_" ^ original_type_str ^ "_to_" ^ cast_type_str in
            A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [ e ]))
          | _, _ -> A.(AilEcast (empty_qualifiers, bt_to_ail_ctype bt, e))
        in
        (ail_expr_, b, s)
    in
    dest d (b, s, mk_expr ail_expr_)


let cn_to_ail_expr_internal
  : type a.
    _ CF.Cn.cn_datatype list -> (C.union_tag * C.ctype) list -> IT.t -> a dest -> a
  =
  fun dts globals cn_expr d -> cn_to_ail_expr_aux_internal None None dts globals cn_expr d


let cn_to_ail_expr
  (dts : _ CF.Cn.cn_datatype list)
  (globals : (C.union_tag * C.ctype) list)
  (pred_sym_opt : Sym.t option)
  (it : IT.t)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
  =
  cn_to_ail_expr_aux_internal None pred_sym_opt dts globals it PassBack


let cn_to_ail_expr_internal_with_pred_name
  : type a.
    Sym.sym option ->
    _ CF.Cn.cn_datatype list ->
    (C.union_tag * C.ctype) list ->
    IT.t ->
    a dest ->
    a
  =
  fun pred_name_opt dts globals cn_expr d ->
  cn_to_ail_expr_aux_internal None pred_name_opt dts globals cn_expr d


let create_member (ctype, id) = (id, (empty_attributes, None, empty_qualifiers, ctype))

let generate_tag_definition dt_members =
  let ail_dt_members =
    List.map (fun (id, cn_type) -> (cn_to_ail_base_type cn_type, id)) dt_members
  in
  (* TODO: Check if something called tag already exists *)
  let members = List.map create_member ail_dt_members in
  C.(StructDef (members, None))


let generate_struct_definition ?(lc = true) (constructor, members) =
  let constr_sym =
    if lc then
      Sym.fresh_pretty (String.lowercase_ascii (Sym.pp_string constructor))
    else
      constructor
  in
  (constr_sym, (Cerb_location.unknown, empty_attributes, generate_tag_definition members))


let cn_to_ail_pred_records map_bindings =
  let flipped_bindings = List.map (fun (ms, sym) -> (sym, ms)) map_bindings in
  List.map generate_struct_definition flipped_bindings


(* Generic map get for structs, datatypes and records *)
(* Used in generate_struct_map_get, generate_datatype_map_get and generate_record_map_get *)
let generate_map_get sym =
  let ctype_str = "struct_" ^ Sym.pp_string sym in
  let fn_str = "cn_map_get_" ^ ctype_str in
  let void_ptr_type = C.(mk_ctype_pointer empty_qualifiers (mk_ctype Void)) in
  let param1_sym = Sym.fresh_pretty "m" in
  let param2_sym = Sym.fresh_pretty "key" in
  let param_syms = [ param1_sym; param2_sym ] in
  let param_types =
    List.map bt_to_ail_ctype [ BT.Map (Integer, Struct sym); BT.Integer ]
  in
  let param_types =
    List.map (fun ctype -> (empty_qualifiers, ctype, false)) param_types
  in
  let fn_sym = Sym.fresh_pretty fn_str in
  let ret_sym = Sym.fresh_pretty "ret" in
  let ret_binding = create_binding ret_sym void_ptr_type in
  let key_val_mem =
    mk_expr A.(AilEmemberofptr (mk_expr (AilEident param2_sym), Id.id "val"))
  in
  let ht_get_fcall =
    mk_expr
      A.(
        AilEcall
          ( mk_expr (AilEident (Sym.fresh_pretty "ht_get")),
            [ mk_expr (AilEident param1_sym); mk_expr (AilEunary (Address, key_val_mem)) ]
          ))
  in
  let ret_decl = A.(AilSdeclaration [ (ret_sym, Some ht_get_fcall) ]) in
  let ret_ident = A.(AilEident ret_sym) in
  (* Function body *)
  let if_cond =
    mk_expr
      A.(
        AilEbinary
          ( mk_expr A.(AilEconst (ConstantInteger (IConstant (Z.of_int 0, Decimal, None)))),
            Eq,
            mk_expr ret_ident ))
  in
  let default_fcall =
    A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty ("default_" ^ ctype_str))), []))
  in
  let cast_expr = A.(AilEcast (empty_qualifiers, void_ptr_type, mk_expr default_fcall)) in
  let if_stmt =
    A.(
      AilSif
        ( if_cond,
          mk_stmt (AilSreturn (mk_expr cast_expr)),
          mk_stmt (AilSreturn (mk_expr ret_ident)) ))
  in
  let ret_type = void_ptr_type in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( Cerb_location.unknown,
        empty_attributes,
        A.(
          Decl_function
            (false, (empty_qualifiers, ret_type), param_types, false, false, false)) ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( Cerb_location.unknown,
        0,
        empty_attributes,
        param_syms,
        mk_stmt A.(AilSblock ([ ret_binding ], List.map mk_stmt [ ret_decl; if_stmt ])) )
    )
  in
  [ (decl, def) ]


let cn_to_ail_datatype ?(first = false) (cn_datatype : cn_datatype)
  : Locations.t * A.sigma_tag_definition list
  =
  let enum_sym = generate_sym_with_suffix cn_datatype.cn_dt_name in
  let constructor_syms = List.map fst cn_datatype.cn_dt_cases in
  let generate_enum_member sym =
    let doc = CF.Pp_ail.pp_id sym in
    let str = CF.Pp_utils.to_plain_string doc in
    let str = String.uppercase_ascii str in
    Id.id str
  in
  let enum_member_syms = List.map generate_enum_member constructor_syms in
  let attr : CF.Annot.attribute =
    { attr_ns = None; attr_id = Id.id "enum"; attr_args = [] }
  in
  let attrs = CF.Annot.Attrs [ attr ] in
  let enum_members =
    List.map
      (fun sym -> (sym, (empty_attributes, None, empty_qualifiers, mk_ctype C.Void)))
      enum_member_syms
  in
  let enum_tag_definition = C.(UnionDef enum_members) in
  let enum = (enum_sym, (Cerb_location.unknown, attrs, enum_tag_definition)) in
  let cntype_sym = Sym.fresh_pretty "cntype" in
  let cntype_pointer = C.(Pointer (empty_qualifiers, mk_ctype (Struct cntype_sym))) in
  let extra_members tag_type =
    [ create_member (mk_ctype tag_type, Id.id "tag");
      create_member (mk_ctype cntype_pointer, Id.id "cntype")
    ]
  in
  let structs =
    List.map (fun c -> generate_struct_definition c) cn_datatype.cn_dt_cases
  in
  let structs =
    if first then (
      let generic_dt_struct =
        ( generic_cn_dt_sym,
          ( Cerb_location.unknown,
            empty_attributes,
            C.(StructDef (extra_members C.(Basic (Integer (Signed Int_))), None)) ) )
      in
      let cntype_struct =
        (cntype_sym, (Cerb_location.unknown, empty_attributes, C.(StructDef ([], None))))
      in
      generic_dt_struct :: cntype_struct :: structs)
    else (* TODO: Add members to cntype_struct as we go along? *)
      structs
  in
  let union_sym = generate_sym_with_suffix ~suffix:"_union" cn_datatype.cn_dt_name in
  let union_def_members =
    List.map
      (fun sym ->
        let lc_sym = Sym.fresh_pretty (String.lowercase_ascii (Sym.pp_string sym)) in
        create_member
          ( mk_ctype C.(Pointer (empty_qualifiers, mk_ctype (Struct lc_sym))),
            create_id_from_sym ~lowercase:true sym ))
      constructor_syms
  in
  let union_def = C.(UnionDef union_def_members) in
  let union_member = create_member (mk_ctype C.(Union union_sym), Id.id "u") in
  let structs =
    structs
    @ [ (union_sym, (Cerb_location.unknown, empty_attributes, union_def));
        ( cn_datatype.cn_dt_name,
          ( Cerb_location.unknown,
            empty_attributes,
            C.(
              StructDef
                ( extra_members C.(Basic (Integer (Enum enum_sym))) @ [ union_member ],
                  None )) ) )
      ]
  in
  (cn_datatype.cn_dt_magic_loc, enum :: structs)


let generate_datatype_equality_function (cn_datatype : cn_datatype)
  : (A.sigma_declaration * 'a A.sigma_function_definition) list
  =
  (*
     type cn_datatype 'a = <|
     cn_dt_loc: Loc.t;
     cn_dt_name: 'a;
     cn_dt_cases: list ('a * list (cn_base_type 'a * Symbol.identifier));
     |>
  *)
  let dt_sym = cn_datatype.cn_dt_name in
  let fn_sym = Sym.fresh_pretty ("struct_" ^ Sym.pp_string dt_sym ^ "_equality") in
  let param1_sym = Sym.fresh_pretty "x" in
  let param2_sym = Sym.fresh_pretty "y" in
  let id_tag = Id.id "tag" in
  let param_syms = [ param1_sym; param2_sym ] in
  let param_type =
    ( empty_qualifiers,
      mk_ctype (C.Pointer (empty_qualifiers, mk_ctype (Struct dt_sym))),
      false )
  in
  let tag_check_cond =
    A.(
      AilEbinary
        ( mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), id_tag)),
          Ne,
          mk_expr (AilEmemberofptr (mk_expr (AilEident param2_sym), id_tag)) ))
  in
  let false_it = IT.(IT (Const (Z (Z.of_int 0)), BT.Bool, Cerb_location.unknown)) in
  (* Adds conversion function *)
  let _, _, e1 = cn_to_ail_expr_internal [] [] false_it PassBack in
  let return_false = A.(AilSreturn e1) in
  let rec generate_equality_expr members sym1 sym2 =
    match members with
    | [] -> IT.(IT (Const (Z (Z.of_int 1)), BT.Bool, Cerb_location.unknown))
    | (id, cn_bt) :: ms ->
      let sym1_it = IT.(IT (Sym sym1, BT.(Loc ()), Cerb_location.unknown)) in
      let sym2_it = IT.(IT (Sym sym2, BT.(Loc ()), Cerb_location.unknown)) in
      let lhs =
        IT.(
          IT (StructMember (sym1_it, id), cn_base_type_to_bt cn_bt, Cerb_location.unknown))
      in
      let rhs =
        IT.(
          IT (StructMember (sym2_it, id), cn_base_type_to_bt cn_bt, Cerb_location.unknown))
      in
      let eq_it = IT.(IT (Binop (EQ, lhs, rhs), BT.Bool, Cerb_location.unknown)) in
      let remaining = generate_equality_expr ms sym1 sym2 in
      IT.(IT (Binop (And, eq_it, remaining), BT.Bool, Cerb_location.unknown))
  in
  let create_case (constructor, members) =
    let enum_str =
      Sym.pp_string (generate_sym_with_suffix ~suffix:"" ~uppercase:true constructor)
    in
    let attribute : CF.Annot.attribute =
      { attr_ns = None;
        attr_id = CF.Symbol.Identifier (Cerb_location.unknown, enum_str);
        attr_args = []
      }
    in
    let x_constr_sym = Sym.fresh () in
    let y_constr_sym = Sym.fresh () in
    let constr_syms = [ x_constr_sym; y_constr_sym ] in
    let bs, ss =
      match members with
      | [] -> ([], [])
      | _ ->
        let lc_constr_sym =
          generate_sym_with_suffix ~suffix:"" ~lowercase:true constructor
        in
        let constr_id = create_id_from_sym ~lowercase:true constructor in
        let constr_struct_type =
          mk_ctype C.(Pointer (empty_qualifiers, mk_ctype (Struct lc_constr_sym)))
        in
        let bindings =
          List.map (fun sym -> create_binding sym constr_struct_type) constr_syms
        in
        let memberof_ptr_es =
          List.map
            (fun sym -> mk_expr A.(AilEmemberofptr (mk_expr (AilEident sym), Id.id "u")))
            param_syms
        in
        let decls =
          List.map
            (fun (constr_sym, e) ->
              A.(
                AilSdeclaration
                  [ (constr_sym, Some (mk_expr (AilEmemberof (e, constr_id)))) ]))
            (List.combine constr_syms memberof_ptr_es)
        in
        (bindings, List.map mk_stmt decls)
    in
    let equality_expr = generate_equality_expr members x_constr_sym y_constr_sym in
    let _, _, e = cn_to_ail_expr_internal [] [] equality_expr PassBack in
    let return_stat = mk_stmt A.(AilSreturn e) in
    let ail_case =
      A.(AilScase (Nat_big_num.zero, mk_stmt (AilSblock (bs, ss @ [ return_stat ]))))
    in
    A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [ attribute ], ail_case))
  in
  let switch_stmt =
    A.(
      AilSswitch
        ( mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), id_tag)),
          mk_stmt (AilSblock ([], List.map create_case cn_datatype.cn_dt_cases)) ))
  in
  let tag_if_stmt =
    A.(AilSif (mk_expr tag_check_cond, mk_stmt return_false, mk_stmt switch_stmt))
  in
  let ret_type = bt_to_ail_ctype BT.Bool in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( cn_datatype.cn_dt_loc,
        empty_attributes,
        A.(
          Decl_function
            ( false,
              (empty_qualifiers, ret_type),
              [ param_type; param_type ],
              false,
              false,
              false )) ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( cn_datatype.cn_dt_loc,
        0,
        empty_attributes,
        param_syms,
        mk_stmt A.(AilSblock ([], [ mk_stmt tag_if_stmt ])) ) )
  in
  [ (decl, def) ]


let generate_datatype_map_get (cn_datatype : cn_datatype) =
  let cn_sym = cn_datatype.cn_dt_name in
  generate_map_get cn_sym


let generate_datatype_default_function (cn_datatype : cn_datatype) =
  let cn_sym = cn_datatype.cn_dt_name in
  let fn_str = "default_struct_" ^ Sym.pp_string cn_sym in
  let cn_struct_ctype = C.(Struct cn_sym) in
  let cn_struct_ptr_ctype =
    mk_ctype C.(Pointer (empty_qualifiers, mk_ctype cn_struct_ctype))
  in
  let fn_sym = Sym.fresh_pretty fn_str in
  let alloc_fcall = mk_alloc_expr cn_struct_ctype in
  let res_sym = Sym.fresh_pretty "res" in
  let res_ident = mk_expr A.(AilEident res_sym) in
  let res_binding = create_binding res_sym cn_struct_ptr_ctype in
  let res_decl = A.(AilSdeclaration [ (res_sym, Some alloc_fcall) ]) in
  let rec get_non_recursive_constr_and_ms = function
    | [] -> failwith "Datatype default generation failure: datatype has no constructors"
    | ((_, members) as x) :: xs ->
      let _ids, basetypes = List.split members in
      if List.mem BT.equal (Datatype cn_sym) (List.map cn_base_type_to_bt basetypes) then
        get_non_recursive_constr_and_ms xs
      else
        x
  in
  (*
     datatype Tree {
        Tree_Empty {i32 k (* for working out what to do with constructor members *)},
        Tree_Node {i32 k, datatype tree l, datatype tree r}
      }

      ->

      struct tree * default_struct_tree(void) {
        struct tree *res = alloc(sizeof(struct tree));
        res->tag = TREE_EMPTY;
        res->u.tree_empty = alloc(sizeof(struct tree_empty));
        res->u.tree_empty->k = default_cn_bits_i32();
        return res;
      }
  *)
  let constructor, members = get_non_recursive_constr_and_ms cn_datatype.cn_dt_cases in
  let enum_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true constructor in
  let enum_str = Sym.pp_string enum_sym in
  let attribute : CF.Annot.attribute =
    { attr_ns = None;
      attr_id = CF.Symbol.Identifier (Cerb_location.unknown, enum_str);
      attr_args = []
    }
  in
  let enum_ident = mk_expr A.(AilEident enum_sym) in
  let res_tag_assign =
    A.(
      AilSexpr
        (mk_expr
           (AilEassign (mk_expr (AilEmemberofptr (res_ident, Id.id "tag")), enum_ident))))
  in
  let res_tag_assign_stat =
    A.(
      AnnotatedStatement
        (Cerb_location.unknown, CF.Annot.Attrs [ attribute ], res_tag_assign))
  in
  let lc_constr_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true constructor in
  let res_u = A.(AilEmemberofptr (res_ident, Id.id "u")) in
  let res_u_constr =
    mk_expr (AilEmemberof (mk_expr res_u, create_id_from_sym lc_constr_sym))
  in
  let constr_alloc_assign_ =
    A.(
      AilSexpr
        (mk_expr (AilEassign (res_u_constr, mk_alloc_expr C.(Struct lc_constr_sym)))))
  in
  let member_assign_info =
    List.map
      (fun (id, cn_bt) ->
        let bt = cn_base_type_to_bt cn_bt in
        let member_ctype_str_opt = get_underscored_typedef_string_from_bt bt in
        let default_fun_str =
          match member_ctype_str_opt with
          | Some member_ctype_str -> "default_" ^ member_ctype_str
          | None ->
            Printf.printf "%s\n" (Pp.plain (BT.pp bt));
            failwith "no underscored typedef string found"
        in
        let fcall =
          A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty default_fun_str)), []))
        in
        (id, mk_expr fcall))
      members
  in
  let member_assign_stats =
    List.map
      (fun (id, rhs) ->
        A.(
          AilSexpr
            (mk_expr (AilEassign (mk_expr (AilEmemberofptr (res_u_constr, id)), rhs)))))
      member_assign_info
  in
  (* Function body *)
  let return_stmt = A.(AilSreturn res_ident) in
  let ret_type = cn_struct_ptr_ctype in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( Cerb_location.unknown,
        empty_attributes,
        A.(Decl_function (false, (empty_qualifiers, ret_type), [], false, false, false))
      ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( Cerb_location.unknown,
        0,
        empty_attributes,
        [],
        mk_stmt
          A.(
            AilSblock
              ( [ res_binding ],
                mk_stmt res_decl
                :: res_tag_assign_stat
                :: List.map
                     mk_stmt
                     ((constr_alloc_assign_ :: member_assign_stats) @ [ return_stmt ]) ))
      ) )
  in
  [ (decl, def) ]


(* STRUCTS *)
let generate_struct_equality_function
  ?(is_record = false)
  dts
  ((sym, (_loc, _attrs, tag_def)) : A.sigma_tag_definition)
  : (A.sigma_declaration * 'a A.sigma_function_definition) list
  =
  match tag_def with
  | C.StructDef (members, _) ->
    let cn_sym = if is_record then sym else generate_sym_with_suffix ~suffix:"_cn" sym in
    let cn_struct_ctype = mk_ctype C.(Struct cn_sym) in
    let cn_struct_ptr_ctype = mk_ctype C.(Pointer (empty_qualifiers, cn_struct_ctype)) in
    let fn_sym = Sym.fresh_pretty ("struct_" ^ Sym.pp_string cn_sym ^ "_equality") in
    let param_syms = [ Sym.fresh_pretty "x"; Sym.fresh_pretty "y" ] in
    let param_type =
      (empty_qualifiers, mk_ctype (C.Pointer (empty_qualifiers, mk_ctype Void)), false)
    in
    let cast_param_syms =
      List.map (fun sym -> generate_sym_with_suffix ~suffix:"_cast" sym) param_syms
    in
    let cast_bindings =
      List.map (fun sym -> create_binding sym cn_struct_ptr_ctype) cast_param_syms
    in
    let cast_assignments =
      List.map
        (fun (cast_sym, sym) ->
          A.(
            AilSdeclaration
              [ ( cast_sym,
                  Some
                    (mk_expr
                       (AilEcast
                          (empty_qualifiers, cn_struct_ptr_ctype, mk_expr (AilEident sym))))
                )
              ]))
        (List.combine cast_param_syms param_syms)
    in
    (* Function body *)
    let generate_member_equality (id, (_, _, _, ctype)) =
      let _doc = CF.Pp_ail.pp_ctype ~executable_spec:true empty_qualifiers ctype in
      (* Printf.printf "%s\n" (CF.Pp_utils.to_plain_pretty_string doc); *)
      let sct_opt = Sctypes.of_ctype ctype in
      let sct =
        match sct_opt with
        | Some t -> t
        | None ->
          (* Printf.printf "None case\n"; *)
          failwith "Bad sctype"
      in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
      let args =
        List.map
          (fun cast_sym -> mk_expr (AilEmemberofptr (mk_expr (AilEident cast_sym), id)))
          cast_param_syms
      in
      (* List length of args guaranteed to be 2 by construction *)
      assert (List.length args == 2);
      let equality_fn_call =
        get_equality_fn_call bt (List.nth args 0) (List.nth args 1) dts
      in
      mk_expr equality_fn_call
    in
    let member_equality_exprs = List.map generate_member_equality members in
    let cn_bool_and_sym = Sym.fresh_pretty "cn_bool_and" in
    let ail_and_binop =
      List.fold_left
        (fun e1 e2 ->
          mk_expr A.(AilEcall (mk_expr (AilEident cn_bool_and_sym), [ e1; e2 ])))
        cn_bool_true_expr
        member_equality_exprs
    in
    (* let rec remove_true_const ail_binop = match rm_expr ail_binop with
       | A.(AilEbinary (e1, And, e2)) -> (match rm_expr e1 with
       | A.AilEconst (ConstantInteger (IConstant (_, Decimal, Some B))) -> e2
       | _ -> mk_expr A.(AilEbinary (remove_true_const e1, And, e2)))
       | _ -> failwith "Incorrect form"
       in
       let ail_and_binop = remove_true_const ail_and_binop in *)
    let return_stmt = A.(AilSreturn ail_and_binop) in
    let ret_type = bt_to_ail_ctype BT.Bool in
    (* Generating function declaration *)
    let decl =
      ( fn_sym,
        ( Cerb_location.unknown,
          empty_attributes,
          A.(
            Decl_function
              ( false,
                (empty_qualifiers, ret_type),
                [ param_type; param_type ],
                false,
                false,
                false )) ) )
    in
    (* Generating function definition *)
    let def =
      ( fn_sym,
        ( Cerb_location.unknown,
          0,
          empty_attributes,
          param_syms,
          mk_stmt
            A.(
              AilSblock
                (cast_bindings, List.map mk_stmt (cast_assignments @ [ return_stmt ]))) )
      )
    in
    [ (decl, def) ]
  | C.UnionDef _ -> []


let generate_struct_default_function
  ?(is_record = false)
  _dts
  ((sym, (_loc, _attrs, tag_def)) : A.sigma_tag_definition)
  : (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list
  =
  match tag_def with
  | C.StructDef (members, _) ->
    let cn_sym = if is_record then sym else generate_sym_with_suffix ~suffix:"_cn" sym in
    let fn_str = "default_struct_" ^ Sym.pp_string cn_sym in
    let cn_struct_ctype = C.(Struct cn_sym) in
    let cn_struct_ptr_ctype =
      mk_ctype C.(Pointer (empty_qualifiers, mk_ctype cn_struct_ctype))
    in
    let fn_sym = Sym.fresh_pretty fn_str in
    let alloc_fcall = mk_alloc_expr cn_struct_ctype in
    let ret_sym = Sym.fresh () in
    let ret_binding = create_binding ret_sym cn_struct_ptr_ctype in
    let ret_decl = A.(AilSdeclaration [ (ret_sym, Some alloc_fcall) ]) in
    let ret_ident = A.(AilEident ret_sym) in
    (* Function body *)
    let generate_member_default_assign (id, (_, _, _, ctype)) =
      let ctype = if is_record then get_ctype_without_ptr ctype else ctype in
      let lhs = A.(AilEmemberofptr (mk_expr ret_ident, id)) in
      let sct_opt = Sctypes.of_ctype ctype in
      let sct = match sct_opt with Some t -> t | None -> failwith "Bad sctype" in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
      let member_ctype_str_opt = get_underscored_typedef_string_from_bt ~is_record bt in
      let default_fun_str =
        match member_ctype_str_opt with
        | Some member_ctype_str -> "default_" ^ member_ctype_str
        | None ->
          Printf.printf "%s\n" (Pp.plain (BT.pp bt));
          failwith "no underscored typedef string found"
      in
      let fcall =
        A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty default_fun_str)), []))
      in
      A.(AilSexpr (mk_expr (AilEassign (mk_expr lhs, mk_expr fcall))))
    in
    let member_default_assigns = List.map generate_member_default_assign members in
    let return_stmt = A.(AilSreturn (mk_expr ret_ident)) in
    let ret_type = cn_struct_ptr_ctype in
    (* Generating function declaration *)
    let decl =
      ( fn_sym,
        ( Cerb_location.unknown,
          empty_attributes,
          A.(Decl_function (false, (empty_qualifiers, ret_type), [], false, false, false))
        ) )
    in
    (* Generating function definition *)
    let def =
      ( fn_sym,
        ( Cerb_location.unknown,
          0,
          empty_attributes,
          [],
          mk_stmt
            A.(
              AilSblock
                ( [ ret_binding ],
                  List.map mk_stmt ((ret_decl :: member_default_assigns) @ [ return_stmt ])
                )) ) )
    in
    [ (decl, def) ]
  | C.UnionDef _ -> []


let generate_struct_map_get ((sym, (_loc, _attrs, tag_def)) : A.sigma_tag_definition)
  : (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list
  =
  match tag_def with
  | C.StructDef _ ->
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    generate_map_get cn_sym
  | C.UnionDef _ -> []


let generate_struct_conversion_to_function
  ((sym, (_loc, _attrs, tag_def)) : A.sigma_tag_definition)
  : (A.sigma_declaration * 'a A.sigma_function_definition) list
  =
  match tag_def with
  | C.StructDef (members, _) ->
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    let cn_struct_ctype = C.(Struct cn_sym) in
    let fn_sym =
      Sym.fresh_pretty (Option.get (get_conversion_to_fn_str (BT.Struct sym)))
    in
    let param_sym = sym in
    let param_type = (empty_qualifiers, mk_ctype C.(Struct sym), false) in
    (* Function body *)
    let res_sym = Sym.fresh_pretty "res" in
    let res_binding =
      create_binding
        res_sym
        (mk_ctype (C.Pointer (empty_qualifiers, mk_ctype cn_struct_ctype)))
    in
    let alloc_fcall = mk_alloc_expr cn_struct_ctype in
    let res_assign = A.(AilSdeclaration [ (res_sym, Some alloc_fcall) ]) in
    let generate_member_assignment (id, (_, _, _, ctype)) =
      let rhs = A.(AilEmemberof (mk_expr (AilEident param_sym), id)) in
      let sct_opt = Sctypes.of_ctype ctype in
      let sct = match sct_opt with Some t -> t | None -> failwith "Bad sctype" in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
      let rhs = wrap_with_convert_to ~sct rhs bt in
      let lhs = A.(AilEmemberofptr (mk_expr (AilEident res_sym), id)) in
      A.(AilSexpr (mk_expr (AilEassign (mk_expr lhs, mk_expr rhs))))
    in
    let member_assignments = List.map generate_member_assignment members in
    let return_stmt = A.(AilSreturn (mk_expr (AilEident res_sym))) in
    let ret_type = bt_to_ail_ctype (BT.Struct sym) in
    (* Generating function declaration *)
    let decl =
      ( fn_sym,
        ( Cerb_location.unknown,
          empty_attributes,
          A.(
            Decl_function
              (false, (empty_qualifiers, ret_type), [ param_type ], false, false, false))
        ) )
    in
    (* Generating function definition *)
    let def =
      ( fn_sym,
        ( Cerb_location.unknown,
          0,
          empty_attributes,
          [ param_sym ],
          mk_stmt
            A.(
              AilSblock
                ( [ res_binding ],
                  List.map mk_stmt ((res_assign :: member_assignments) @ [ return_stmt ])
                )) ) )
    in
    [ (decl, def) ]
  | C.UnionDef _ -> []


let generate_struct_conversion_from_function
  ((sym, (_loc, _attrs, tag_def)) : A.sigma_tag_definition)
  : (A.sigma_declaration * 'a A.sigma_function_definition) list
  =
  match tag_def with
  | C.StructDef (members, _) ->
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    let struct_ctype = mk_ctype C.(Struct sym) in
    let fn_sym =
      Sym.fresh_pretty (Option.get (get_conversion_from_fn_str (BT.Struct sym)))
    in
    let param_sym = sym in
    let param_type =
      ( empty_qualifiers,
        C.(mk_ctype_pointer no_qualifiers (mk_ctype (Struct cn_sym))),
        false )
    in
    (* Function body *)
    let res_sym = Sym.fresh_pretty "res" in
    let res_binding = create_binding res_sym struct_ctype in
    let res_assign = A.(AilSdeclaration [ (res_sym, None) ]) in
    let generate_member_assignment (id, (_, _, _, ctype)) =
      let rhs = A.(AilEmemberofptr (mk_expr (AilEident param_sym), id)) in
      let sct_opt = Sctypes.of_ctype ctype in
      let sct = match sct_opt with Some t -> t | None -> failwith "Bad sctype" in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
      let lhs = A.(AilEmemberof (mk_expr (AilEident res_sym), id)) in
      match (bt, sct) with
      | BT.Map (_k_bt, v_bt), Sctypes.Array (_v_sct, Some sz) ->
        A.(
          AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr
                      (AilEident
                         (Sym.fresh_named (Option.get (get_conversion_from_fn_str bt)))),
                    List.map
                      mk_expr
                      [ lhs;
                        rhs;
                        AilEident
                          (Sym.fresh_named (Option.get (get_type_underscored_str v_bt)));
                        AilEconst
                          (ConstantInteger (IConstant (Z.of_int sz, Decimal, None)))
                      ] ))))
      | BT.Map _, _ -> failwith "unsupported map types"
      | _ ->
        let rhs = wrap_with_convert_from ~sct rhs bt in
        A.(AilSexpr (mk_expr (AilEassign (mk_expr lhs, mk_expr rhs))))
    in
    let member_assignments = List.map generate_member_assignment members in
    let return_stmt = A.(AilSreturn (mk_expr (AilEident res_sym))) in
    (* Generating function declaration *)
    let decl =
      ( fn_sym,
        ( Cerb_location.unknown,
          empty_attributes,
          A.(
            Decl_function
              ( false,
                (empty_qualifiers, struct_ctype),
                [ param_type ],
                false,
                false,
                false )) ) )
    in
    (* Generating function definition *)
    let def =
      ( fn_sym,
        ( Cerb_location.unknown,
          0,
          empty_attributes,
          [ param_sym ],
          mk_stmt
            A.(
              AilSblock
                ( [ res_binding ],
                  List.map mk_stmt ((res_assign :: member_assignments) @ [ return_stmt ])
                )) ) )
    in
    [ (decl, def) ]
  | C.UnionDef _ -> []


(* RECORDS *)
let generate_record_equality_function dts (sym, (members : BT.member_types))
  : (A.sigma_declaration * 'a A.sigma_function_definition) list
  =
  let cn_sym = sym in
  let cn_struct_ctype = mk_ctype C.(Struct cn_sym) in
  let cn_struct_ptr_ctype = mk_ctype C.(Pointer (empty_qualifiers, cn_struct_ctype)) in
  let fn_sym = Sym.fresh_pretty ("struct_" ^ Sym.pp_string cn_sym ^ "_equality") in
  let param_syms = [ Sym.fresh_pretty "x"; Sym.fresh_pretty "y" ] in
  let param_type =
    (empty_qualifiers, mk_ctype (C.Pointer (empty_qualifiers, mk_ctype Void)), false)
  in
  let cast_param_syms =
    List.map (fun sym -> generate_sym_with_suffix ~suffix:"_cast" sym) param_syms
  in
  let cast_bindings =
    List.map (fun sym -> create_binding sym cn_struct_ptr_ctype) cast_param_syms
  in
  let cast_assignments =
    List.map
      (fun (cast_sym, sym) ->
        A.(
          AilSdeclaration
            [ ( cast_sym,
                Some
                  (mk_expr
                     (AilEcast
                        (empty_qualifiers, cn_struct_ptr_ctype, mk_expr (AilEident sym))))
              )
            ]))
      (List.combine cast_param_syms param_syms)
  in
  (* Function body *)
  let generate_member_equality (id, bt) =
    let args =
      List.map
        (fun cast_sym -> mk_expr (AilEmemberofptr (mk_expr (AilEident cast_sym), id)))
        cast_param_syms
    in
    (* List length of args guaranteed to be 2 by construction *)
    assert (List.length args == 2);
    let equality_fn_call =
      get_equality_fn_call bt (List.nth args 0) (List.nth args 1) dts
    in
    mk_expr equality_fn_call
  in
  let member_equality_exprs = List.map generate_member_equality members in
  let cn_bool_and_sym = Sym.fresh_pretty "cn_bool_and" in
  let ail_and_binop =
    List.fold_left
      (fun e1 e2 ->
        mk_expr A.(AilEcall (mk_expr (AilEident cn_bool_and_sym), [ e1; e2 ])))
      cn_bool_true_expr
      member_equality_exprs
  in
  (* let rec remove_true_const ail_binop = match rm_expr ail_binop with
     | A.(AilEbinary (e1, And, e2)) -> (match rm_expr e1 with
     | A.AilEconst (ConstantInteger (IConstant (_, Decimal, Some B))) -> e2
     | _ -> mk_expr A.(AilEbinary (remove_true_const e1, And, e2)))
     | _ -> failwith "Incorrect form"
     in
     let ail_and_binop = remove_true_const ail_and_binop in *)
  let return_stmt = A.(AilSreturn ail_and_binop) in
  let ret_type = bt_to_ail_ctype BT.Bool in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( Cerb_location.unknown,
        empty_attributes,
        A.(
          Decl_function
            ( false,
              (empty_qualifiers, ret_type),
              [ param_type; param_type ],
              false,
              false,
              false )) ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( Cerb_location.unknown,
        0,
        empty_attributes,
        param_syms,
        mk_stmt
          A.(
            AilSblock
              (cast_bindings, List.map mk_stmt (cast_assignments @ [ return_stmt ]))) ) )
  in
  [ (decl, def) ]


let generate_record_default_function _dts (sym, (members : BT.member_types))
  : (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list
  =
  let cn_sym = sym in
  let fn_str = "default_struct_" ^ Sym.pp_string cn_sym in
  let cn_struct_ctype = C.(Struct cn_sym) in
  let cn_struct_ptr_ctype =
    mk_ctype C.(Pointer (empty_qualifiers, mk_ctype cn_struct_ctype))
  in
  let fn_sym = Sym.fresh_pretty fn_str in
  let alloc_fcall = mk_alloc_expr cn_struct_ctype in
  let ret_sym = Sym.fresh () in
  let ret_binding = create_binding ret_sym cn_struct_ptr_ctype in
  let ret_decl = A.(AilSdeclaration [ (ret_sym, Some alloc_fcall) ]) in
  let ret_ident = A.(AilEident ret_sym) in
  (* Function body *)
  let generate_member_default_assign (id, bt) =
    let lhs = A.(AilEmemberofptr (mk_expr ret_ident, id)) in
    let member_ctype_str_opt = get_underscored_typedef_string_from_bt bt in
    let default_fun_str =
      match member_ctype_str_opt with
      | Some member_ctype_str -> "default_" ^ member_ctype_str
      | None ->
        Printf.printf "%s\n" (Pp.plain (BT.pp bt));
        failwith "no underscored typedef string found"
    in
    let fcall =
      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty default_fun_str)), []))
    in
    A.(AilSexpr (mk_expr (AilEassign (mk_expr lhs, mk_expr fcall))))
  in
  let member_default_assigns = List.map generate_member_default_assign members in
  let return_stmt = A.(AilSreturn (mk_expr ret_ident)) in
  let ret_type = cn_struct_ptr_ctype in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( Cerb_location.unknown,
        empty_attributes,
        A.(Decl_function (false, (empty_qualifiers, ret_type), [], false, false, false))
      ) )
  in
  (* Generating function definition *)
  let def =
    ( fn_sym,
      ( Cerb_location.unknown,
        0,
        empty_attributes,
        [],
        mk_stmt
          A.(
            AilSblock
              ( [ ret_binding ],
                List.map mk_stmt ((ret_decl :: member_default_assigns) @ [ return_stmt ])
              )) ) )
  in
  [ (decl, def) ]


let generate_record_map_get (sym, _) = generate_map_get sym

let cn_to_ail_struct ((sym, (loc, attrs, tag_def)) : A.sigma_tag_definition)
  : A.sigma_tag_definition list
  =
  match tag_def with
  | C.StructDef (members, opt) ->
    let cn_struct_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    let new_members =
      List.map
        (fun (id, (attrs, alignment, qualifiers, ctype)) ->
          let sct_opt = Sctypes.of_ctype ctype in
          let sct = match sct_opt with Some t -> t | None -> failwith "Bad sctype" in
          let bt =
            BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct
          in
          (id, (attrs, alignment, qualifiers, bt_to_ail_ctype bt)))
        members
    in
    [ (cn_struct_sym, (loc, attrs, C.StructDef (new_members, opt))) ]
  | C.UnionDef _ -> []


(* is_pre used for ownership checking, to see if ownership needs to be taken or put back *)
let cn_to_ail_resource_internal
  ?(is_pre = true)
  ?(is_toplevel = true)
  sym
  dts
  globals
  (preds : (Sym.t * RP.definition) list)
  loc
  =
  let calculate_return_type = function
    | ResourceTypes.Owned (sct, _) ->
      ( Sctypes.to_ctype sct,
        BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct )
    | PName pname ->
      let matching_preds =
        List.filter (fun (pred_sym', _def) -> Sym.equal pname pred_sym') preds
      in
      let pred_sym', pred_def' =
        match matching_preds with [] -> failwith "Predicate not found" | p :: _ -> p
      in
      let cn_bt = bt_to_cn_base_type pred_def'.oarg_bt in
      let ctype =
        match cn_bt with
        | CN_record _members ->
          let pred_record_name = generate_sym_with_suffix ~suffix:"_record" pred_sym' in
          (* records := RecordMap.add members pred_record_name !records; *)
          mk_ctype C.(Pointer (empty_qualifiers, mk_ctype (Struct pred_record_name)))
        | _ -> cn_to_ail_base_type ~pred_sym:(Some pred_sym') cn_bt
      in
      (ctype, pred_def'.oarg_bt)
  in
  (* let make_deref_expr_ e_ = A.(AilEunary (Indirection, mk_expr e_)) in *)
  function
  | ResourceTypes.P p ->
    let ctype, bt = calculate_return_type p.name in
    let b, s, e = cn_to_ail_expr_internal dts globals p.pointer PassBack in
    let enum_str = if is_pre then "GET" else "PUT" in
    let enum_str = if not is_toplevel then "owned_enum" else enum_str in
    let enum_sym = Sym.fresh_pretty enum_str in
    let rhs, bs, ss, _owned_ctype =
      match p.name with
      | Owned (sct, _) ->
        ownership_ctypes := Sctypes.to_ctype sct :: !ownership_ctypes;
        let ct_str = str_of_ctype (Sctypes.to_ctype sct) in
        let ct_str = String.concat "_" (String.split_on_char ' ' ct_str) in
        let owned_fn_name = "owned_" ^ ct_str in
        (* Hack with enum as sym *)
        let enum_val_get = IT.(IT (Sym enum_sym, BT.Integer, Cerb_location.unknown)) in
        let fn_call_it =
          IT.IT
            ( Apply (Sym.fresh_pretty owned_fn_name, [ p.pointer; enum_val_get ]),
              BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct,
              Cerb_location.unknown )
        in
        let bs', ss', e' = cn_to_ail_expr_internal dts globals fn_call_it PassBack in
        let binding = create_binding sym (bt_to_ail_ctype bt) in
        (e', binding :: bs', ss', Some (Sctypes.to_ctype sct))
      | PName pname ->
        let bs, ss, es =
          list_split_three
            (List.map (fun it -> cn_to_ail_expr_internal dts globals it PassBack) p.iargs)
        in
        let error_msg_update_stats_ =
          generate_error_msg_info_update_stats ~cn_source_loc_opt:(Some loc) ()
        in
        let fcall =
          A.(
            AilEcall
              (mk_expr (AilEident pname), (e :: es) @ [ mk_expr (AilEident enum_sym) ]))
        in
        let binding = create_binding sym (bt_to_ail_ctype ~pred_sym:(Some pname) bt) in
        ( mk_expr fcall,
          binding :: List.concat bs,
          List.concat ss @ error_msg_update_stats_,
          None )
    in
    let s_decl =
      match rm_ctype ctype with
      | C.Void -> A.(AilSexpr rhs)
      | _ -> A.(AilSdeclaration [ (sym, Some rhs) ])
    in
    (b @ bs, s @ ss @ [ s_decl ])
  | ResourceTypes.Q q ->
    (*
       Input is expr of the form:
      take sym = each (integer q.q; q.permission){ Owned(q.pointer + (q.q * q.step)) }
    *)
    let b1, s1, _e1 = cn_to_ail_expr_internal dts globals q.pointer PassBack in
    (*
       Generating a loop of the form:
    <set q.q to start value>
    while (q.permission) {
      *(sym + q.q * q.step) = *(q.pointer + q.q * q.step);
      q.q++;
    }
    *)
    let i_sym, i_bt = q.q in
    let start_cond = get_leftmost_of_and_expr q.permission in
    let start_expr = generate_start_expr start_cond (fst q.q) in
    let start_expr =
      IT.IT
        (IT.Cast (IT.bt start_expr, start_expr), IT.bt start_expr, Cerb_location.unknown)
    in
    let _, _, e_start = cn_to_ail_expr_internal dts globals start_expr PassBack in
    let end_cond = get_leftmost_of_and_expr (get_rest_of_expr_r q.permission) in
    let if_stat_cond = get_rest_of_expr_r (get_rest_of_expr_r q.permission) in
    let while_loop_cond =
      IT.IT (Binop (And, start_cond, end_cond), BT.Bool, Cerb_location.unknown)
    in
    let _, _, while_cond_expr =
      cn_to_ail_expr_internal dts globals while_loop_cond PassBack
    in
    let _, _, if_cond_expr = cn_to_ail_expr_internal dts globals if_stat_cond PassBack in
    let cn_integer_ptr_ctype = bt_to_ail_ctype i_bt in
    (* let convert_to_cn_integer_sym =
       Sym.fresh_pretty (Option.get (get_conversion_to_fn_str BT.Integer))
       in *)
    let b2, s2, _e2 = cn_to_ail_expr_internal dts globals q.permission PassBack in
    let b3, s3, _e3 = cn_to_ail_expr_internal dts globals q.step PassBack in
    (* let conversion_fcall = A.(AilEcall (mk_expr (AilEident convert_to_cn_integer_sym), [e_start])) in *)
    let start_binding = create_binding i_sym cn_integer_ptr_ctype in
    let start_assign = A.(AilSdeclaration [ (i_sym, Some e_start) ]) in
    (* let (end_binding, end_assign) = convert_to_cn_binop e_end in *)

    (* let q_times_step = A.(AilEbinary (mk_expr (AilEident i_sym), Arithmetic Mul, e3)) in *)
    (* let gen_add_expr_ e_ =
       A.(AilEbinary (mk_expr e_, Arithmetic Add, mk_expr q_times_step))
       in *)
    (* let sym_add_expr = make_deref_expr_ (gen_add_expr_ A.(AilEident sym)) in *)
    let return_ctype, _return_bt = calculate_return_type q.name in
    (* Translation of q.pointer *)
    let i_it = IT.IT (IT.(Sym i_sym), i_bt, Cerb_location.unknown) in
    let step_binop =
      IT.IT (IT.(Binop (Mul, i_it, q.step)), i_bt, Cerb_location.unknown)
    in
    let value_it =
      IT.IT (IT.(Binop (Add, q.pointer, step_binop)), BT.(Loc ()), Cerb_location.unknown)
    in
    let b4, s4, e4 = cn_to_ail_expr_internal dts globals value_it PassBack in
    let ptr_add_sym = Sym.fresh () in
    let cn_pointer_return_type = bt_to_ail_ctype BT.(Loc ()) in
    let ptr_add_binding = create_binding ptr_add_sym cn_pointer_return_type in
    let ptr_add_stat = A.(AilSdeclaration [ (ptr_add_sym, Some e4) ]) in
    let enum_str = if is_pre then "GET" else "PUT" in
    let enum_str = if not is_toplevel then "owned_enum" else enum_str in
    let enum_sym = Sym.fresh_pretty enum_str in
    let rhs, bs, ss, _owned_ctype =
      match q.name with
      | Owned (sct, _) ->
        ownership_ctypes := Sctypes.to_ctype sct :: !ownership_ctypes;
        let sct_str = str_of_ctype (Sctypes.to_ctype sct) in
        let sct_str = String.concat "_" (String.split_on_char ' ' sct_str) in
        let owned_fn_name = "owned_" ^ sct_str in
        let ptr_add_it = IT.(IT (Sym ptr_add_sym, BT.(Loc ()), Cerb_location.unknown)) in
        (* Hack with enum as sym *)
        let enum_val_get = IT.(IT (Sym enum_sym, BT.Integer, Cerb_location.unknown)) in
        let fn_call_it =
          IT.IT
            ( Apply (Sym.fresh_pretty owned_fn_name, [ ptr_add_it; enum_val_get ]),
              BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct,
              Cerb_location.unknown )
        in
        let bs', ss', e' = cn_to_ail_expr_internal dts globals fn_call_it PassBack in
        (e', bs', ss', Some (Sctypes.to_ctype sct))
      | PName pname ->
        let bs, ss, es =
          list_split_three
            (List.map (fun it -> cn_to_ail_expr_internal dts globals it PassBack) q.iargs)
        in
        let error_msg_update_stats_ =
          generate_error_msg_info_update_stats ~cn_source_loc_opt:(Some loc) ()
        in
        let fcall =
          A.(
            AilEcall
              ( mk_expr (AilEident pname),
                (mk_expr (AilEident ptr_add_sym) :: es) @ [ mk_expr (AilEident enum_sym) ]
              ))
        in
        (mk_expr fcall, List.concat bs, List.concat ss @ error_msg_update_stats_, None)
    in
    let typedef_name = get_typedef_string (bt_to_ail_ctype i_bt) in
    let incr_func_name =
      match typedef_name with Some str -> str ^ "_increment" | None -> ""
    in
    let increment_fn_sym = Sym.fresh_pretty incr_func_name in
    let increment_stat =
      A.(
        AilSexpr
          (mk_expr
             (AilEcall
                (mk_expr (AilEident increment_fn_sym), [ mk_expr (AilEident i_sym) ]))))
    in
    let bs', ss' =
      match rm_ctype return_ctype with
      | C.Void ->
        let void_pred_call = A.(AilSexpr rhs) in
        let if_stat =
          A.(
            AilSif
              ( wrap_with_convert_from_cn_bool if_cond_expr,
                mk_stmt
                  (AilSblock
                     ( [ ptr_add_binding ],
                       List.map mk_stmt [ ptr_add_stat; void_pred_call ] )),
                mk_stmt (AilSblock ([], [ mk_stmt AilSskip ])) ))
        in
        let while_loop =
          A.(
            AilSwhile
              ( wrap_with_convert_from_cn_bool while_cond_expr,
                mk_stmt (AilSblock ([], List.map mk_stmt [ if_stat; increment_stat ])),
                0 ))
        in
        let ail_block =
          A.(AilSblock ([], List.map mk_stmt [ start_assign; while_loop ]))
        in
        ([], [ ail_block ])
      | _ ->
        (* TODO: Change to mostly use index terms rather than Ail directly - avoids duplication between these functions and cn_internal_to_ail *)
        let cn_map_type =
          mk_ctype ~annots:[ CF.Annot.Atypedef (Sym.fresh_pretty "cn_map") ] C.Void
        in
        let sym_binding =
          create_binding sym (mk_ctype C.(Pointer (empty_qualifiers, cn_map_type)))
        in
        let create_call =
          A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "map_create")), []))
        in
        let sym_decl = A.(AilSdeclaration [ (sym, Some (mk_expr create_call)) ]) in
        let i_ident_expr = A.(AilEident i_sym) in
        let i_bt_str =
          match get_typedef_string (bt_to_ail_ctype i_bt) with
          | Some str -> str
          | None -> ""
        in
        let i_expr =
          if i_bt == BT.Integer then
            i_ident_expr
          else
            A.(
              AilEcall
                ( mk_expr
                    (AilEident (Sym.fresh_pretty ("cast_" ^ i_bt_str ^ "_to_cn_integer"))),
                  [ mk_expr i_ident_expr ] ))
        in
        let map_set_expr_ =
          A.(
            AilEcall
              ( mk_expr (AilEident (Sym.fresh_pretty "cn_map_set")),
                List.map mk_expr [ AilEident sym; i_expr ] @ [ rhs ] ))
        in
        let if_stat =
          A.(
            AilSif
              ( wrap_with_convert_from_cn_bool if_cond_expr,
                mk_stmt
                  (AilSblock
                     ( ptr_add_binding :: b4,
                       List.map
                         mk_stmt
                         (s4 @ [ ptr_add_stat; AilSexpr (mk_expr map_set_expr_) ]) )),
                mk_stmt (AilSblock ([], [ mk_stmt AilSskip ])) ))
        in
        let while_loop =
          A.(
            AilSwhile
              ( wrap_with_convert_from_cn_bool while_cond_expr,
                mk_stmt A.(AilSblock ([], List.map mk_stmt [ if_stat; increment_stat ])),
                0 ))
        in
        let ail_block =
          A.(AilSblock ([], List.map mk_stmt [ start_assign; while_loop ]))
        in
        ([ sym_binding ], [ sym_decl; ail_block ])
    in
    (b1 @ b2 @ b3 @ [ start_binding ] @ bs' @ bs, s1 @ s2 @ s3 @ ss @ ss')


let cn_to_ail_logical_constraint_internal
  : type a.
    _ CF.Cn.cn_datatype list ->
    (C.union_tag * C.ctype) list ->
    a dest ->
    LC.logical_constraint ->
    a
  =
  fun dts globals d lc ->
  match lc with
  | LogicalConstraints.T it -> cn_to_ail_expr_internal dts globals it d
  | LogicalConstraints.Forall ((sym, bt), it) ->
    let cond_it, t =
      match IT.term it with
      | Binop (Implies, it, it') -> (it, it')
      | _ -> failwith "Incorrect form of forall logical constraint term"
    in
    (match IT.term t with
     | Good _ -> dest d ([], [], cn_bool_true_expr)
     | _ ->
       (* Assume cond_it is of a particular form *)
       (*
          Input:

          each (bt s; cond_it) {t}

          
          Want to translate to:
          bool b = true; // b should be a fresh sym each time

          {
            signed int s = r_start;
            while (sym < r_end) {
              b = b && t;
              sym++;
            }   
          }
          
          assign/return/assert/passback b
       *)
       let start_cond = get_leftmost_of_and_expr cond_it in
       let start_expr = generate_start_expr start_cond sym in
       let start_expr =
         IT.IT
           ( IT.Cast (IT.bt start_expr, start_expr),
             IT.bt start_expr,
             Cerb_location.unknown )
       in
       let _, _, e_start = cn_to_ail_expr_internal dts globals start_expr PassBack in
       let end_cond = get_leftmost_of_and_expr (get_rest_of_expr_r cond_it) in
       let if_stat_cond = get_rest_of_expr_r (get_rest_of_expr_r cond_it) in
       let while_loop_cond =
         IT.IT (Binop (And, start_cond, end_cond), BT.Bool, Cerb_location.unknown)
       in
       let _, _, while_cond_expr =
         cn_to_ail_expr_internal dts globals while_loop_cond PassBack
       in
       let _, _, if_cond_expr =
         cn_to_ail_expr_internal dts globals if_stat_cond PassBack
       in
       let t_translated = cn_to_ail_expr_internal dts globals t PassBack in
       let bs, ss, e =
         gen_bool_while_loop
           sym
           bt
           (rm_expr e_start)
           while_cond_expr
           ~if_cond_opt:(Some if_cond_expr)
           t_translated
       in
       dest d (bs, ss, e))


let cn_to_ail_logical_constraint
  (dts : _ CF.Cn.cn_datatype list)
  (globals : (C.union_tag * C.ctype) list)
  (lc : LC.t)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
  =
  cn_to_ail_logical_constraint_internal dts globals PassBack lc


let rec generate_record_opt pred_sym = function
  | BT.Record members ->
    let members' = List.map (fun (id, bt) -> (id, bt_to_cn_base_type bt)) members in
    let record_sym = generate_sym_with_suffix ~suffix:"_record" pred_sym in
    Some (generate_struct_definition ~lc:false (record_sym, members'))
  | BT.Tuple ts ->
    let members = List.map (fun t -> (create_id_from_sym (Sym.fresh ()), t)) ts in
    generate_record_opt pred_sym (BT.Record members)
  | _ -> None


(* TODO: Finish with rest of function - maybe header file with A.Decl_function (cn.h?) *)
let cn_to_ail_function_internal
  (fn_sym, (lf_def : LogicalFunctions.definition))
  (cn_datatypes : A.sigma_cn_datatype list)
  (cn_functions : A.sigma_cn_function list)
  : ((Locations.t * A.sigma_declaration)
    * CF.GenTypes.genTypeCategory A.sigma_function_definition option)
    * A.sigma_tag_definition option
  =
  let ret_type = bt_to_ail_ctype ~pred_sym:(Some fn_sym) lf_def.return_bt in
  (* let ret_type = mk_ctype C.(Pointer (empty_qualifiers, ret_type)) in *)
  let bs, ail_func_body_opt =
    match lf_def.definition with
    | Def it | Rec_Def it ->
      let bs, ss =
        cn_to_ail_expr_internal_with_pred_name (Some fn_sym) cn_datatypes [] it Return
      in
      (bs, Some (List.map mk_stmt ss))
    | Uninterp ->
      failwith
        "Uninterpreted CN functions not supported at runtime. Please provide a concrete \
         function definition"
  in
  let ail_record_opt = generate_record_opt fn_sym lf_def.return_bt in
  let params = List.map (fun (sym, bt) -> (sym, bt_to_ail_ctype bt)) lf_def.args in
  let param_syms, param_types = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  let matched_cn_functions =
    List.filter
      (fun (cn_fun : (A.ail_identifier, C.ctype) CF.Cn.cn_function) ->
        Sym.equal cn_fun.cn_func_name fn_sym)
      cn_functions
  in
  (* Unsafe - check if list has an element *)
  let loc = (List.nth matched_cn_functions 0).cn_func_magic_loc in
  (* Generating function declaration *)
  let decl =
    ( fn_sym,
      ( lf_def.loc,
        empty_attributes,
        A.(
          Decl_function
            (false, (empty_qualifiers, ret_type), param_types, false, false, false)) ) )
  in
  (* Generating function definition *)
  let def =
    match ail_func_body_opt with
    | Some ail_func_body ->
      Some
        ( fn_sym,
          ( lf_def.loc,
            0,
            empty_attributes,
            param_syms,
            mk_stmt A.(AilSblock (bs, ail_func_body)) ) )
    | None -> None
  in
  (((loc, decl), def), ail_record_opt)


let rec cn_to_ail_lat_internal ?(is_toplevel = true) dts pred_sym_opt globals preds
  = function
  | LAT.Define ((name, it), _info, lat) ->
    let ctype = bt_to_ail_ctype (IT.bt it) in
    let binding = create_binding name ctype in
    let decl = A.(AilSdeclaration [ (name, None) ]) in
    let b1, s1 =
      cn_to_ail_expr_internal_with_pred_name pred_sym_opt dts globals it (AssignVar name)
    in
    let b2, s2 = cn_to_ail_lat_internal ~is_toplevel dts pred_sym_opt globals preds lat in
    (b1 @ b2 @ [ binding ], (decl :: s1) @ s2)
  | LAT.Resource ((name, (ret, _bt)), (loc, _str_opt), lat) ->
    let b1, s1 =
      cn_to_ail_resource_internal ~is_pre:true ~is_toplevel name dts globals preds loc ret
    in
    let b2, s2 = cn_to_ail_lat_internal ~is_toplevel dts pred_sym_opt globals preds lat in
    (b1 @ b2, s1 @ s2)
  | LAT.Constraint (lc, (loc, _str_opt), lat) ->
    let b1, s, e = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    let ss = s @ generate_cn_assert ~cn_source_loc_opt:(Some loc) e in
    let b2, s2 = cn_to_ail_lat_internal ~is_toplevel dts pred_sym_opt globals preds lat in
    (b1 @ b2, ss @ s2)
  | LAT.I it ->
    let bs, ss =
      cn_to_ail_expr_internal_with_pred_name pred_sym_opt dts globals it Return
    in
    (bs, ss)


let cn_to_ail_predicate_internal
  (pred_sym, (rp_def : ResourcePredicates.definition))
  dts
  globals
  preds
  cn_preds
  =
  let ret_type = bt_to_ail_ctype ~pred_sym:(Some pred_sym) rp_def.oarg_bt in
  let rec clause_translate (clauses : RP.clause list) =
    match clauses with
    | [] -> ([], [])
    | c :: cs ->
      let bs, ss =
        cn_to_ail_lat_internal
          ~is_toplevel:false
          dts
          (Some pred_sym)
          globals
          preds
          c.packing_ft
      in
      (match c.guard with
       | IT (Const (Bool true), _, _) ->
         let bs'', ss'' = clause_translate cs in
         (bs @ bs'', ss @ ss'')
       | _ ->
         let _b1, _s1, e =
           cn_to_ail_expr_internal_with_pred_name (Some pred_sym) dts [] c.guard PassBack
         in
         let bs'', ss'' = clause_translate cs in
         let conversion_from_cn_bool =
           A.(AilEcall (mk_expr (AilEident convert_from_cn_bool_sym), [ e ]))
         in
         let ail_if_stat =
           A.(
             AilSif
               ( mk_expr conversion_from_cn_bool,
                 mk_stmt (AilSblock (bs, List.map mk_stmt ss)),
                 mk_stmt (AilSblock (bs'', List.map mk_stmt ss'')) ))
         in
         ([], [ ail_if_stat ]))
  in
  let bs, ss =
    match rp_def.clauses with Some clauses -> clause_translate clauses | None -> ([], [])
  in
  let pred_body = List.map mk_stmt ss in
  let ail_record_opt = generate_record_opt pred_sym rp_def.oarg_bt in
  let params =
    List.map
      (fun (sym, bt) -> (sym, bt_to_ail_ctype bt))
      ((rp_def.pointer, BT.(Loc ())) :: rp_def.iargs)
  in
  let enum_param_sym = Sym.fresh_pretty "owned_enum" in
  let params =
    params
    @ [ ( enum_param_sym,
          mk_ctype C.(Basic (Integer (Enum (Sym.fresh_pretty "OWNERSHIP")))) )
      ]
  in
  let param_syms, param_types = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  (* Generating function declaration *)
  let decl =
    ( pred_sym,
      ( rp_def.loc,
        empty_attributes,
        A.(
          Decl_function
            (false, (empty_qualifiers, ret_type), param_types, false, false, false)) ) )
  in
  (* Generating function definition *)
  let def =
    ( pred_sym,
      (rp_def.loc, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (bs, pred_body)))
    )
  in
  let matched_cn_preds =
    List.filter
      (fun (cn_pred : (A.ail_identifier, C.ctype) CF.Cn.cn_predicate) ->
        Sym.equal cn_pred.cn_pred_name pred_sym)
      cn_preds
  in
  (* Unsafe - check if list has an element *)
  let loc = (List.nth matched_cn_preds 0).cn_pred_magic_loc in
  (((loc, decl), def), ail_record_opt)


let rec cn_to_ail_predicates_internal pred_def_list dts globals preds cn_preds
  : ((Locations.t * A.sigma_declaration)
    * CF.GenTypes.genTypeCategory A.sigma_function_definition)
      list
    * A.sigma_tag_definition option list
  =
  match pred_def_list with
  | [] -> ([], [])
  | p :: ps ->
    let d, r = cn_to_ail_predicate_internal p dts globals preds cn_preds in
    let ds, rs = cn_to_ail_predicates_internal ps dts globals preds cn_preds in
    (d :: ds, r :: rs)


(* TODO: Add destination passing? *)
let rec cn_to_ail_post_aux_internal dts globals preds = function
  | LRT.Define ((name, it), (_loc, _), t) ->
    (* Printf.printf "LRT.Define\n"; *)
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in
    let new_lrt =
      Core_to_mucore.fn_spec_instrumentation_sym_subst_lrt (name, IT.bt it, new_name) t
    in
    let binding = create_binding new_name (bt_to_ail_ctype (IT.bt it)) in
    let decl = A.(AilSdeclaration [ (new_name, None) ]) in
    let b1, s1 = cn_to_ail_expr_internal dts globals it (AssignVar new_name) in
    let b2, s2 = cn_to_ail_post_aux_internal dts globals preds new_lrt in
    (b1 @ b2 @ [ binding ], (decl :: s1) @ s2)
  | LRT.Resource ((name, (re, bt)), (loc, _str_opt), t) ->
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in
    let b1, s1 =
      cn_to_ail_resource_internal ~is_pre:false new_name dts globals preds loc re
    in
    let new_lrt =
      Core_to_mucore.fn_spec_instrumentation_sym_subst_lrt (name, bt, new_name) t
    in
    let b2, s2 = cn_to_ail_post_aux_internal dts globals preds new_lrt in
    (b1 @ b2, s1 @ s2)
  | LRT.Constraint (lc, (loc, _str_opt), t) ->
    let b1, s, e = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    let ss = s @ generate_cn_assert ~cn_source_loc_opt:(Some loc) e in
    let b2, s2 = cn_to_ail_post_aux_internal dts globals preds t in
    (b1 @ b2, ss @ s2)
  | LRT.I -> ([], [])


let cn_to_ail_post_internal dts globals preds (RT.Computational (_bound, _oinfo, t)) =
  let bs, ss = cn_to_ail_post_aux_internal dts globals preds t in
  (bs, List.map mk_stmt ss)


(* TODO: Add destination passing *)
let cn_to_ail_cnstatement_internal
  : type a.
    _ CF.Cn.cn_datatype list ->
    (C.union_tag * C.ctype) list ->
    a dest ->
    Cnprog.statement ->
    a * bool
  =
  fun dts globals d cnstatement ->
  let default_res_for_dest = empty_for_dest d in
  match cnstatement with
  | Cnprog.Pack_unpack (_pack_unpack, _pt) -> (default_res_for_dest, true)
  | To_from_bytes (_to_from, _res) -> (default_res_for_dest, true)
  | Have _lc -> failwith "TODO Have"
  | Instantiate (_to_instantiate, _it) -> (default_res_for_dest, true)
  | Split_case _ -> (default_res_for_dest, true)
  | Extract (_, _, _it) -> (default_res_for_dest, true)
  | Unfold (_fsym, _args) -> (default_res_for_dest, true) (* fsym is a function symbol *)
  | Apply (_fsym, _args) -> (default_res_for_dest, true) (* fsym is a lemma symbol *)
  | Assert lc -> (cn_to_ail_logical_constraint_internal dts globals d lc, false)
  | Inline _ -> failwith "TODO Inline"
  | Print _t -> (default_res_for_dest, true)


let rec cn_to_ail_cnprog_internal_aux dts globals = function
  | Cnprog.Let (_loc, (name, { ct; pointer }), prog) ->
    let b1, s, e = cn_to_ail_expr_internal dts globals pointer PassBack in
    let cn_ptr_deref_sym = Sym.fresh_pretty "cn_pointer_deref" in
    let ctype_sym =
      Sym.fresh_pretty
        (Pp.plain
           (CF.Pp_ail.pp_ctype
              ~executable_spec:true
              empty_qualifiers
              (Sctypes.to_ctype ct)))
    in
    let cn_ptr_deref_fcall =
      A.(
        AilEcall
          (mk_expr (AilEident cn_ptr_deref_sym), [ e; mk_expr (AilEident ctype_sym) ]))
    in
    let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type ct in
    let ctype = bt_to_ail_ctype bt in
    let binding = create_binding name ctype in
    let ail_stat_ =
      A.(
        AilSdeclaration
          [ (name, Some (mk_expr (wrap_with_convert_to cn_ptr_deref_fcall bt))) ])
    in
    let (b2, ss), no_op = cn_to_ail_cnprog_internal_aux dts globals prog in
    (* let ail_stat_ = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident name), mk_expr ail_deref_expr_)))) in *)
    if no_op then
      (([], []), true)
    else
      ((b1 @ (binding :: b2), s @ (ail_stat_ :: ss)), false)
    (* if no_op then
    ((loc', [], []), true)
  else
    ((loc', b1 @ b2 @ [binding], s @ ail_stat_ :: ss), false) *)
  | Statement (loc, stmt) ->
    let (bs, ss), no_op = cn_to_ail_cnstatement_internal dts globals (Assert loc) stmt in
    ((bs, ss), no_op)


let cn_to_ail_cnprog_internal dts globals cn_prog =
  let (bs, ss), _ = cn_to_ail_cnprog_internal_aux dts globals cn_prog in
  (bs, ss)


let cn_to_ail_statements dts globals (loc, cn_progs) =
  let bs_and_ss =
    List.map (fun prog -> cn_to_ail_cnprog_internal dts globals prog) cn_progs
  in
  let bs, ss = List.split bs_and_ss in
  (loc, (List.concat bs, List.concat ss))


let prepend_to_precondition ail_executable_spec (b1, s1) =
  let b2, s2 = ail_executable_spec.pre in
  { ail_executable_spec with pre = (b1 @ b2, s1 @ s2) }


(* Precondition and postcondition translation - LAT.I case means precondition translation finished *)
let rec cn_to_ail_lat_internal_2 with_ownership_checking dts globals preds c_return_type
  = function
  | LAT.Define ((name, it), _info, lat) ->
    let ctype = bt_to_ail_ctype (IT.bt it) in
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in
    let new_lat =
      Core_to_mucore.fn_spec_instrumentation_sym_subst_lat (name, IT.bt it, new_name) lat
    in
    (* let ctype = mk_ctype C.(Pointer (empty_qualifiers, ctype)) in *)
    let binding = create_binding new_name ctype in
    let decl = A.(AilSdeclaration [ (new_name, None) ]) in
    let b1, s1 = cn_to_ail_expr_internal dts globals it (AssignVar new_name) in
    let ail_executable_spec =
      cn_to_ail_lat_internal_2
        with_ownership_checking
        dts
        globals
        preds
        c_return_type
        new_lat
    in
    prepend_to_precondition ail_executable_spec (binding :: b1, decl :: s1)
  | LAT.Resource ((name, (ret, bt)), (loc, _str_opt), lat) ->
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in
    let b1, s1 =
      cn_to_ail_resource_internal ~is_pre:true new_name dts globals preds loc ret
    in
    let new_lat =
      Core_to_mucore.fn_spec_instrumentation_sym_subst_lat (name, bt, new_name) lat
    in
    let ail_executable_spec =
      cn_to_ail_lat_internal_2
        with_ownership_checking
        dts
        globals
        preds
        c_return_type
        new_lat
    in
    prepend_to_precondition ail_executable_spec (b1, s1)
  | LAT.Constraint (lc, (loc, _str_opt), lat) ->
    let b1, s, e = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    let ss = s @ generate_cn_assert ~cn_source_loc_opt:(Some loc) e in
    let ail_executable_spec =
      cn_to_ail_lat_internal_2 with_ownership_checking dts globals preds c_return_type lat
    in
    prepend_to_precondition ail_executable_spec (b1, ss)
  (* Postcondition *)
  | LAT.I (post, stats) ->
    let rec remove_duplicates locs stats =
      match stats with
      | [] -> []
      | (loc, s) :: ss ->
        let loc_equality x y =
          String.equal
            (Cerb_location.location_to_string x)
            (Cerb_location.location_to_string y)
        in
        if List.mem loc_equality loc locs then
          remove_duplicates locs ss
        else
          (loc, s) :: remove_duplicates (loc :: locs) ss
    in
    (* let substitution : IT.t Subst.t = {replace = [(Sym.fresh_pretty "return", IT.(IT (Sym (Sym.fresh_pretty "__cn_ret"), BT.Unit)))]; relevant = SymSet.empty} in *)
    (* let post_with_ret = RT.subst substitution post in *)
    let return_cn_binding, return_cn_decl =
      match rm_ctype c_return_type with
      | C.Void -> ([], [])
      | _ ->
        let return_cn_sym = Sym.fresh_pretty "return_cn" in
        let sct_opt = Sctypes.of_ctype c_return_type in
        let sct =
          match sct_opt with Some t -> t | None -> failwith "No sctype conversion"
        in
        let bt =
          BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct
        in
        let real_return_ctype = bt_to_ail_ctype bt in
        let return_cn_binding = create_binding return_cn_sym real_return_ctype in
        let cn_ret_ail_expr_ = A.(AilEident (Sym.fresh_pretty "__cn_ret")) in
        let return_cn_decl =
          A.(
            AilSdeclaration
              [ ( return_cn_sym,
                  Some (mk_expr (wrap_with_convert_to ~sct cn_ret_ail_expr_ bt)) )
              ])
        in
        ([ return_cn_binding ], [ mk_stmt return_cn_decl ])
    in
    let stats = remove_duplicates [] stats in
    let ail_statements =
      List.map (fun stat_pair -> cn_to_ail_statements dts globals stat_pair) stats
    in
    let post_bs, post_ss = cn_to_ail_post_internal dts globals preds post in
    let ownership_stat_ =
      if with_ownership_checking then (
        let cn_stack_depth_decr_stat_ =
          mk_stmt
            (A.AilSexpr
               (mk_expr (AilEcall (mk_expr (AilEident OE.cn_stack_depth_decr_sym), []))))
        in
        [ cn_stack_depth_decr_stat_ ])
      else
        []
    in
    let block =
      A.(
        AilSblock (return_cn_binding @ post_bs, return_cn_decl @ post_ss @ ownership_stat_))
    in
    { pre = ([], []); post = ([], [ block ]); in_stmt = ail_statements }


let rec cn_to_ail_pre_post_aux_internal
  with_ownership_checking
  dts
  preds
  globals
  c_return_type
  = function
  | AT.Computational ((sym, bt), _info, at) ->
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    let cn_ctype = bt_to_ail_ctype bt in
    let binding = create_binding cn_sym cn_ctype in
    let rhs = wrap_with_convert_to A.(AilEident sym) bt in
    let decl = A.(AilSdeclaration [ (cn_sym, Some (mk_expr rhs)) ]) in
    let subst_at =
      Core_to_mucore.fn_spec_instrumentation_sym_subst_at (sym, bt, cn_sym) at
    in
    let ail_executable_spec =
      cn_to_ail_pre_post_aux_internal
        with_ownership_checking
        dts
        preds
        globals
        c_return_type
        subst_at
    in
    prepend_to_precondition ail_executable_spec ([ binding ], [ decl ])
  | AT.L lat ->
    cn_to_ail_lat_internal_2 with_ownership_checking dts globals preds c_return_type lat


let cn_to_ail_pre_post_internal ~with_ownership_checking dts preds globals c_return_type
  = function
  | Some internal ->
    let ail_executable_spec =
      cn_to_ail_pre_post_aux_internal
        with_ownership_checking
        dts
        preds
        globals
        c_return_type
        internal
    in
    let extra_stats_ =
      if with_ownership_checking then (
        let cn_stack_depth_incr_stat_ =
          A.AilSexpr
            (mk_expr (AilEcall (mk_expr (AilEident OE.cn_stack_depth_incr_sym), [])))
        in
        [ cn_stack_depth_incr_stat_ ])
      else
        []
    in
    prepend_to_precondition ail_executable_spec ([], extra_stats_)
  | None -> empty_ail_executable_spec
