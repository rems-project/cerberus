module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
open CF.Cn
open Compile
open Executable_spec_utils
open PPrint
module A=CF.AilSyntax
module C=CF.Ctype
module BT=BaseTypes

let generic_cn_dt_sym = Sym.fresh_pretty "cn_datatype"

let rec bt_to_cn_base_type = function
| BT.Unit -> CN_unit
| BT.Bool -> CN_bool
| BT.Integer -> CN_integer
| BT.Real -> CN_real
| BT.CType -> failwith "TODO"
| BT.Loc -> CN_loc
| BT.Struct tag -> CN_struct tag
| BT.Datatype tag -> CN_datatype tag
| BT.Record member_types -> failwith "TODO"
  (* CN_record (List.map_snd of_basetype member_types) *)
| BT.Map (bt1, bt2) -> CN_map (bt_to_cn_base_type bt1, bt_to_cn_base_type bt2)
| BT.List bt -> CN_list (bt_to_cn_base_type bt)
| BT.Tuple bts -> CN_tuple (List.map bt_to_cn_base_type bts)
| BT.Set bt -> CN_set (bt_to_cn_base_type bt)
| _ -> failwith "TODO"


(* TODO: Complete *)
let rec cn_to_ail_base_type = 
  let generate_ail_array bt = C.(Array (Ctype ([], cn_to_ail_base_type bt), None)) in 
  function
  | CN_unit -> C.Void
  | CN_bool -> C.(Basic (Integer Bool))
  | CN_integer -> C.(Basic (Integer (Signed Int_))) (* TODO: Discuss integers *)
  (* | CN_real -> failwith "TODO" *)
  | CN_loc -> C.(Pointer (empty_qualifiers, Ctype ([], Void))) (* Casting all CN pointers to void star *)
  | CN_struct sym -> C.(Struct sym)
  (* | CN_record of list (cn_base_type 'a * Symbol.identifier) *)
  | CN_datatype sym -> C.(Pointer (empty_qualifiers, Ctype ([], Struct sym)))
  (* | CN_map of cn_base_type 'a * cn_base_type 'a *)
  | CN_list bt -> generate_ail_array bt (* TODO: What is the optional second pair element for? Have just put None for now *)
  (* | CN_tuple of list (cn_base_type 'a) *)
  | CN_set bt -> generate_ail_array bt
  | _ -> failwith "TODO"

let cn_to_ail_binop = function
  | CN_add -> A.(Arithmetic Add)
  | CN_sub -> A.(Arithmetic Sub)
  | CN_mul -> A.(Arithmetic Mul)
  | CN_div -> A.(Arithmetic Div)
  | CN_equal -> A.Eq
  | CN_inequal -> A.Ne
  | CN_lt -> A.Lt
  | CN_gt -> A.Gt
  | CN_le -> A.Le
  | CN_ge -> A.Ge
  | CN_or -> A.Or
  | CN_and -> A.And
  | CN_map_get -> failwith "TODO"
  


let cn_to_ail_const = function
  | CNConst_NULL -> A.(AilEconst ConstantNull)
  | CNConst_integer n -> A.(AilEconst (ConstantInteger (IConstant (n, Decimal, None))))
  | CNConst_bits ((sign, width), n) ->
      begin match width with
        | 8 | 16 | 32 | 64 ->
            failwith "TODO: RINI"
        | 128 ->
            failwith "TODO: CNConst_bits 128"
        | _ ->
            (* if this occurs, something changed in C_lexer (see cn_integer_width) *)
            assert false
      end
  (* Representing bool as integer with integerSuffix B *)
  | CNConst_bool b -> A.(AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int b), Decimal, Some B))))
  | CNConst_unit -> A.(AilEconst (ConstantIndeterminate C.(Ctype ([], Void))))
 

type 'a dest =
| Assert : (CF.GenTypes.genTypeCategory A.statement_ list) dest
| Return : (CF.GenTypes.genTypeCategory A.statement_ list) dest 
| AssignVar : C.union_tag -> (CF.GenTypes.genTypeCategory A.statement_ list) dest
| PassBack : (CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression_) dest

let dest : type a. a dest -> CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression_ -> a = 
  fun d (s, e) -> 
    match d with
    | Assert -> 
      let assert_stmt = A.(AilSexpr (mk_expr (AilEassert (mk_expr e)))) in
      s @ [assert_stmt]
    | Return ->
      let return_stmt = A.(AilSreturn (mk_expr e)) in
      s @ [return_stmt]
    | AssignVar x -> 
      let assign_stmt = A.(AilSdeclaration [(x, Some (mk_expr e))]) in
      s @ [assign_stmt]
    | PassBack -> (s, e)

let prefix : type a. a dest -> (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list) -> a -> a = 
  fun d (d1, s1) u -> 
    match d, u with 
    | Assert, s2 -> s1 @ s2
    | Return, s2 -> s1 @ s2
    | AssignVar _, s2 -> s1 @ s2
    | PassBack, (s2, e) -> (s1 @ s2, e)


let generate_sym_with_suffix ?(suffix="tag") ?(uppercase=false) constructor =  
  let doc = 
  CF.Pp_ail.pp_id ~executable_spec:true constructor ^^ (!^ "_" ^^ !^ suffix) in 
  let str = 
  CF.Pp_utils.to_plain_string doc in 
  let str = if uppercase then String.uppercase_ascii str else str in
  Sym.fresh_pretty str

(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
let rec cn_to_ail_expr_aux 
: type a. _ option -> (_ Cn.cn_datatype) list -> _ cn_expr -> a dest -> a
= fun const_prop dts (CNExpr (loc, expr_)) d ->
  let cn_to_ail_expr_aux_at_env : type a. _ cn_expr -> string -> a dest -> a
  = (fun e es d ->
      (match es with
        | start_evaluation_scope -> 
          (* let Symbol (digest, nat, _) = CF.Symbol.fresh () in *)
          (* TODO: Make general *)
          let s, ail_expr = cn_to_ail_expr_aux const_prop dts e PassBack in
          let e_cur_nm =
          match ail_expr with
            | A.(AilEident sym) -> CF.Pp_symbol.to_string_pretty sym (* Should only be AilEident sym - function arguments only *)
            | _ -> failwith "Incorrect type of Ail expression"
          in
          let e_old_nm = e_cur_nm ^ "_old" in
          let sym_old = CF.Symbol.Symbol ("", 0, SD_CN_Id e_old_nm) in
          dest d (s, A.(AilEident sym_old))
          ))
  in
  match expr_ with
    | CNExpr_const cn_cst -> 
      let ail_expr_ = cn_to_ail_const cn_cst in
      dest d ([], ail_expr_)
    | CNExpr_value_of_c_atom (sym, _)
    | CNExpr_var sym -> 
      let ail_expr_ = 
      (match const_prop with
        | Some (sym2, cn_const) ->
            if CF.Symbol.equal_sym sym sym2 then
              cn_to_ail_const cn_const
            else
              A.(AilEident sym)
        | None -> A.(AilEident sym)  (* TODO: Check. Need to do more work if this is only a CN var *)
      )
      in
      dest d ([], ail_expr_)
    (* 
    | CNExpr_list es_ -> !^ "[...]" (* Currently unused *)
    *)
    | CNExpr_memberof (e, xs) -> 
      let s, e_ = cn_to_ail_expr_aux const_prop dts e PassBack in
      let ail_expr_ = A.(AilEmemberof (mk_expr e_, xs)) in
      dest d (s, ail_expr_)
    (* 
    | CNExpr_record es -> failwith "TODO"
    | CNExpr_memberupdates (e, _updates) -> !^ "{_ with ...}"
    | CNExpr_arrayindexupdates (e, _updates) -> !^ "_ [ _ = _ ...]"
    *)

    (* TODO: binary operations on structs (esp. equality) *)
    | CNExpr_binop (bop, x, y) -> 
      let s1, e1 = cn_to_ail_expr_aux const_prop dts x PassBack in
      let s2, e2 = cn_to_ail_expr_aux const_prop dts y PassBack in
      let ail_expr_ = A.AilEbinary (mk_expr e1, cn_to_ail_binop bop, mk_expr e2) in 
      dest d (s1 @ s2, ail_expr_)  
    
    | CNExpr_sizeof ct -> 
      let ail_expr_ = A.AilEsizeof (empty_qualifiers, ct) in
      dest d ([], ail_expr_)
    
    | CNExpr_offsetof (tag, member) -> 
      let ail_expr_ = A.(AilEoffsetof (C.(Ctype ([], Struct tag)), member)) in
      dest d ([], ail_expr_)

    (* TODO: Test *)
    | CNExpr_membershift (e, _, member) ->
      let s, e_ = cn_to_ail_expr_aux const_prop dts e PassBack in
      let ail_expr_ = A.(AilEunary (Address, mk_expr (AilEmemberofptr (mk_expr e_, member)))) in 
      dest d (s, ail_expr_)

    | CNExpr_cast (bt, expr) -> 
      let s, e = cn_to_ail_expr_aux const_prop dts expr PassBack in
      let ail_expr_ = A.(AilEcast (empty_qualifiers, C.Ctype ([], cn_to_ail_base_type bt) , (mk_expr e))) in 
      dest d (s, ail_expr_)
    
    | CNExpr_call (sym, exprs) -> 
      let stats_and_exprs = List.map (fun e -> cn_to_ail_expr_aux const_prop dts e PassBack) exprs in
      let (ss, es) = List.split stats_and_exprs in 
      let f = (mk_expr A.(AilEident sym)) in
      let ail_expr_ = A.AilEcall (f, List.map mk_expr es) in 
      dest d (List.concat ss, ail_expr_)
    
    
    | CNExpr_cons (c_nm, exprs) -> 
      let tag_sym = generate_sym_with_suffix c_nm in
      (* Treating enum value as variable name *)
      dest d ([], AilEident tag_sym)   

    (* Should only be integer range *)
    (* TODO: Need to implement CNExpr_match (e, es) - which can be passed via e *)
    | CNExpr_each (sym, _, (r_start, r_end), e) -> 
      let rec create_list_from_range l_start l_end = 
        (if l_start > l_end then 
          []
        else
            l_start :: (create_list_from_range (l_start + 1) l_end)
        )
      in 
      let consts = create_list_from_range (Z.to_int r_start) (Z.to_int r_end) in
      let cn_consts = List.map (fun i -> CNConst_integer (Z.of_int i)) consts in
      let stats_and_exprs = List.map (fun cn_const -> cn_to_ail_expr_aux (Some (sym, cn_const)) dts e PassBack) cn_consts in
      let (ss, es_) = List.split stats_and_exprs in 
      let ail_expr =
        match es_ with
          | (ail_expr1 :: ail_exprs_rest) ->  List.fold_left (fun ae1 ae2 -> A.(AilEbinary (mk_expr ae1, And, mk_expr ae2))) ail_expr1 ail_exprs_rest
          | [] -> failwith "Cannot have empty expression in CN each expression"
      in 
      dest d (List.concat ss, ail_expr)
  
    (* TODO: Add proper error messages for cases handled differently (exprs which are statements in C) *)
    | CNExpr_match (e, es) -> 
      let (s1, e1) = cn_to_ail_expr_aux const_prop dts e PassBack in
      let e1_cast_ctype_ = C.(Pointer (empty_qualifiers, mk_ctype (Struct generic_cn_dt_sym))) in
      let e1_transformed = 
        A.(AilEmemberofptr 
        (mk_expr (AilEcast (empty_qualifiers, mk_ctype e1_cast_ctype_, mk_expr e1)), 
        CF.Symbol.Identifier (Cerb_location.unknown, "tag"))
      )
      in
      let (cases, exprs) = List.split es in
      (* let lhs = List.map (fun e_ -> cn_to_ail_expr const_prop e_ PassBack) cases in *)
      let bindings = [] in
      (* TODO: Return decls too and pass down *)
      let rec generate_switch_stats rhs = 
        (match rhs with
          | [] -> []
          | (((s :: ss)) :: rs) ->  
            (* TODO: Add default case for _ pattern match *)
            let tag_name = "some_tag" in
            (* Generating extra statements for extracting member information for a given datatype constructor *)
            let constructor_name = String.sub tag_name 0 ((String.length tag_name) - 4) in
            let constructor_sym = CF.Symbol.fresh_pretty constructor_name in
            let rec get_members constructor_sym dts = 
              (let rec get_members_helper dt_cases = 
                (match dt_cases with
                  | [] -> None
                  | (constr, members) :: cs -> 
                    let eq = String.equal (Sym.pp_string constr) (Sym.pp_string constructor_sym) in
                    if eq then 
                      Some members
                    else 
                      get_members_helper cs
                )
              in
              match dts with 
              | [] -> failwith "Constructor not found in CN datatypes list" (* Should never reach this case *)
              | dt :: dts_ -> 
                  let members_from_dt = get_members_helper dt.cn_dt_cases in
                  match members_from_dt with 
                    | None -> get_members constructor_sym dts_
                    | Some members -> members
              )
            in
            let members = get_members constructor_sym dts in
            let (member_ids, _) = List.split members in
            let constr_var_sym = Sym.fresh_pretty "_constructor" in

            let member_syms = List.map (fun id -> CF.Symbol.fresh_pretty (Id.s id)) member_ids in

            let create_id_from_sym sym = 
              Id.id (Sym.pp_string sym)
            in

            let rec generate_member_stats member_syms = 
              (match member_syms with 
                | [] -> []
                | sym :: syms -> 
                  let rhs = A.(AilEmemberofptr 
                  (mk_expr (AilEident constr_var_sym), create_id_from_sym sym)) in
                  let ail_expr = A.(AilEassign (mk_expr (AilEident sym), mk_expr rhs)) in
                  (mk_stmt A.(AilSexpr (mk_expr ail_expr))) :: (generate_member_stats syms)
              )
            in

            let member_stats = generate_member_stats member_syms in

            let create_binding sym ctype = 
              A.(sym, ((Cerb_location.unknown, Automatic, false), None, empty_qualifiers, ctype))
            in
            (* <constructor>_tag stored in attribute *)
            let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, tag_name); attr_args = []} in
            let stat_block = 
              (match member_stats with
              | [] -> A.AilSblock ([], List.map mk_stmt (s :: ss))
              | ms -> 
                let cast_type = C.(Pointer (empty_qualifiers, mk_ctype (Struct constructor_sym))) in
                let constr_struct_type = mk_ctype C.(Pointer (empty_qualifiers, mk_ctype (Struct constructor_sym))) in
                let constr_binding = create_binding constr_var_sym constr_struct_type in
                let void_ptr_ctype = mk_ctype C.(Pointer (empty_qualifiers, mk_ctype Void)) in
                let member_bindings = List.map (fun m -> create_binding m void_ptr_ctype) member_syms in
                let constructor_var_assign = mk_stmt A.(AilSdeclaration [(constr_var_sym, Some (mk_expr (AilEcast (empty_qualifiers, mk_ctype cast_type, mk_expr e1))))]) in
                A.(AilSblock (constr_binding :: member_bindings, constructor_var_assign :: ms @ (List.map mk_stmt (s :: ss)))))
            in 
            let ail_case = A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt stat_block)) in
            let ail_case_stmt = A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case)) in
            ail_case_stmt :: (generate_switch_stats rs)
          | _ -> failwith "Wrong pattern")  
      in
      (match d with 
        | Assert -> 
          let rhs = List.map (fun e_ -> cn_to_ail_expr_aux const_prop dts e_ Assert) exprs in 
          let stats = generate_switch_stats rhs in
          let switch = A.(AilSswitch (mk_expr e1_transformed, mk_stmt (AilSblock (bindings, stats)))) in
          s1 @ [switch]
        | Return -> 
          let rhs = List.map (fun e_ -> cn_to_ail_expr_aux const_prop dts e_ Return) exprs in 
          let stats = generate_switch_stats rhs in
          let switch = A.(AilSswitch (mk_expr e1_transformed, mk_stmt (AilSblock (bindings, stats)))) in
          s1 @ [switch]
        | AssignVar x -> failwith "TODO"
        | PassBack -> failwith "TODO")

  
    (* TODO: Might want to consider destination-passing style for if-then-else too (if ternary expressions turn out to look too complicated) *)
    | CNExpr_ite (e1, e2, e3) -> 
        let s1, e1_ = cn_to_ail_expr_aux const_prop dts e1 PassBack in
        let s2, e2_ = cn_to_ail_expr_aux const_prop dts e2 PassBack in
        let s3, e3_ = cn_to_ail_expr_aux const_prop dts e3 PassBack in
        let ail_expr_ = A.AilEcond (mk_expr e1_, Some (mk_expr e2_), mk_expr e3_) in
        dest d (s1 @ s2 @ s3, ail_expr_)
    
    (* 
    | CNExpr_good (ty, e) -> !^ "(good (_, _))" 
    *)


    | CNExpr_let (s, e, body) -> 
      failwith "TODO"
      (* let d1, s1, e1_ = cn_to_ail_expr_aux const_prop e PassBack in  *)
      (* TODO: change second arg (look at Neel code) *)
      (* prefix d (d1, s1) (cn_to_ail_expr_aux const_prop body d) *)

    | CNExpr_deref expr -> 
      let s, e = cn_to_ail_expr_aux const_prop dts expr PassBack in 
      let ail_expr_ = A.(AilEunary (Indirection, mk_expr e)) in 
      dest d (s, ail_expr_)

    | CNExpr_unchanged e -> 
      let e_at_start = CNExpr(loc, CNExpr_at_env (e, start_evaluation_scope)) in
      let s, e_ = cn_to_ail_expr_aux const_prop dts (CNExpr (loc, CNExpr_binop (CN_equal, e, e_at_start))) PassBack in 
      dest d (s, e_)
  
    | CNExpr_at_env (e, es) -> cn_to_ail_expr_aux_at_env e es d 

    | CNExpr_not e -> 
      let s, e_ = cn_to_ail_expr_aux const_prop dts e PassBack in
      let ail_expr_ = A.(AilEunary (Bnot, mk_expr e_)) in 
      dest d (s, ail_expr_)

    | _ -> failwith "TODO"

let cn_to_ail_expr
  : type a. (_ Cn.cn_datatype) list -> _ cn_expr -> a dest -> a
  = fun dts cn_expr d ->
    cn_to_ail_expr_aux None dts cn_expr d


type 'a ail_datatype = {
  structs: (C.union_tag * (Cerb_location.t * CF.Annot.attributes * C.tag_definition)) list;
  decls: (C.union_tag * A.declaration) list;
  stats: ('a A.statement) list;
}



let cn_to_ail_datatype ?(first=false) (cn_datatype : cn_datatype) =
  let enum_sym = generate_sym_with_suffix cn_datatype.cn_dt_name in
  let constructor_syms = List.map fst cn_datatype.cn_dt_cases in
  let generate_enum_member sym = 
    let doc = CF.Pp_ail.pp_id ~executable_spec:true sym in 
    let str = CF.Pp_utils.to_plain_string doc in 
    let str = String.uppercase_ascii str in
    Id.id str
  in
  let enum_member_syms = List.map generate_enum_member constructor_syms in
  let attr : CF.Annot.attribute = {attr_ns = None; attr_id = Id.id "enum"; attr_args = []} in
  let attrs = CF.Annot.Attrs [attr] in
  let enum_members = List.map (fun sym -> (sym, (empty_attributes, None, empty_qualifiers, mk_ctype C.Void))) enum_member_syms in
  let enum_tag_definition = C.(UnionDef enum_members) in
  let enum = (enum_sym, (Cerb_location.unknown, attrs, enum_tag_definition)) in
  let cntype_sym = Sym.fresh_pretty "cntype" in
  let create_member (ctype_, id) =
    (id, (empty_attributes, None, empty_qualifiers, mk_ctype ctype_))
  in
  let cntype_pointer = C.(Pointer (empty_qualifiers, mk_ctype (Struct cntype_sym))) in
  let extra_members tag_type = [
      (create_member (tag_type, Id.id "tag"));
      (create_member (cntype_pointer, Id.id "cntype"))]
  in
  let generate_tag_definition dt_members = 
    let ail_dt_members = List.map (fun (id, cn_type) -> (cn_to_ail_base_type cn_type, id)) dt_members in
    let _void_pointer = C.(Pointer (empty_qualifiers, Ctype ([], Void))) in
    (* TODO: Check if something called tag already exists *)
    let members = List.map create_member ail_dt_members in
    C.(StructDef (members, None))
  in
  let generate_struct_definition (constructor, members) = (constructor, (Cerb_location.unknown, empty_attributes, generate_tag_definition members))
  in
  let structs = List.map (fun c -> generate_struct_definition c) cn_datatype.cn_dt_cases in
  let structs = if first then 
    let generic_dt_struct = 
      (generic_cn_dt_sym, (Cerb_location.unknown, empty_attributes, C.(StructDef (extra_members (C.(Basic (Integer (Signed Int_)))), None))))
    in
    let cntype_struct = (cntype_sym, (Cerb_location.unknown, empty_attributes, C.(StructDef ([], None)))) in
    generic_dt_struct :: cntype_struct :: structs
  else
    (* TODO: Add members to cntype_struct as we go along? *)
    structs
  in
  let union_sym = generate_sym_with_suffix ~suffix:"union" cn_datatype.cn_dt_name in
  let union_member = create_member (C.(Union union_sym), Id.id "u") in
  let structs = structs @ [(cn_datatype.cn_dt_name, (Cerb_location.unknown, empty_attributes, C.(StructDef ((extra_members (C.(Basic (Integer (Enum enum_sym))))) @ [union_member], None))))] in
  (* let rec generate_stats cases count =
    (match cases with 
      | [] -> []
      | (constructor, _) :: cs -> 
        let const = mk_expr (A.(AilEconst (ConstantInteger (IConstant (Z.of_int count, Decimal, None))))) in
        let constructor_sym = generate_constructor_sym constructor in
        (constructor_sym, Some const) :: (generate_stats cs (count + 1))
  )
  in *)
  (* let decl_object = A.(Decl_object ((Automatic, false), None, const_qualifiers, mk_ctype C.(Basic (Integer (Signed Int_))))) in *)
  (* let stats = generate_stats cn_datatype.cn_dt_cases 0 in *)
  (* let generate_enum_from_datatype dt =  *)

  let decls = [] in
  (* let decls = List.map (fun (sym, _) -> (sym, decl_object)) stats in *)
  (* let stats = List.map (fun d -> mk_stmt (A.AilSdeclaration [d])) stats in *)
  let stats = [] in
  {structs = enum :: structs; decls = decls; stats = stats}



(* TODO: Finish with rest of function - maybe header file with A.Decl_function (cn.h?) *)
let cn_to_ail_function cn_function cn_datatypes = 
  let ail_func_body =
  match cn_function.cn_func_body with
    | Some e ->
      let ss = cn_to_ail_expr cn_datatypes e Return in
      List.map mk_stmt ss
    | None -> []
  in
  (* let var_decls = List.map (fun (sym, decl) -> (sym, (Location_ocaml.unknown, empty_attributes, decl))) var_decls in *)
  let ret_type = cn_to_ail_base_type cn_function.cn_func_return_bty in
  let params = List.map (fun (cn_nm, cn_bt) -> (mk_ctype (cn_to_ail_base_type cn_bt), cn_nm)) cn_function.cn_func_args in
  let (param_types, param_names) = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  let func_name = cn_function.cn_func_name in
  (* Generating function declaration *)
  let decl = (func_name, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, mk_ctype ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = (func_name, (Cerb_location.unknown, 0, empty_attributes, param_names, mk_stmt A.(AilSblock ([], ail_func_body)))) in
  (decl, def)

let cn_to_ail_assertion assertion cn_datatypes = 
  match assertion with
  | CN_assert_exp e_ -> 
      (* TODO: Change type signature to keep declarations too *)
      let ss = cn_to_ail_expr cn_datatypes e_ Assert in 
      List.map mk_stmt ss
  | CN_assert_qexp (ident, bTy, e1, e2) -> failwith "TODO"


let cn_to_ail_condition cn_condition type_map cn_datatypes = 
  match cn_condition with
  | CN_cletResource (loc, name, resource) -> ([A.AilSskip], None) (* TODO *)
  | CN_cletExpr (_, name, expr) -> 
    (* TODO: return declarations too *)
    let ss = cn_to_ail_expr cn_datatypes expr (AssignVar name) in
    let sfb_type = SymTable.find type_map name in
    let basetype = SurfaceBaseTypes.to_basetype sfb_type in
    let cn_basetype = bt_to_cn_base_type basetype in
    let ctype = cn_to_ail_base_type cn_basetype in
    (ss, Some (mk_ctype ctype))
  | CN_cconstr (loc, constr) -> 
    let ail_constr = cn_to_ail_assertion constr cn_datatypes in
    let ail_stats_ = List.map rm_stmt ail_constr in
    (ail_stats_, None)
