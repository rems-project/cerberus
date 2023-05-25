[@@@warning "-27"]
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
  (* | CN_datatype sym -> failwith "TODO" *)
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
 

(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
let rec cn_to_ail_expr ?(const_prop=None) (CNExpr (loc, expr_)) =
  let cn_to_ail_expr_at_env = (function
  | (CNExpr_at_env (e, es)) ->
    (match es with
      | start_evaluation_scope -> 
        (* let Symbol (digest, nat, _) = CF.Symbol.fresh () in *)
        (* TODO: Make general *)
        let ail_expr = cn_to_ail_expr ~const_prop e in
        let e_cur_nm =
        match ail_expr with
          | A.(AilEident sym) -> CF.Pp_symbol.to_string_pretty sym (* Should only be AilEident sym - function arguments only *)
          | _ -> failwith "Incorrect type of Ail expression"
        in
        let e_old_nm = e_cur_nm ^ "_old" in
        let sym_old = CF.Symbol.Symbol ("", 0, SD_CN_Id e_old_nm) in
        A.(AilEident sym_old))
  | _ -> 
    failwith "TODO")
  in
  match expr_ with
    | CNExpr_const cn_cst -> cn_to_ail_const cn_cst
    | CNExpr_value_of_c_atom (sym, _)
    | CNExpr_var sym -> 
      (match const_prop with
        | Some (sym2, cn_const) ->
            if CF.Symbol.equal_sym sym sym2 then
              cn_to_ail_const cn_const
            else
              A.(AilEident sym)
        | None -> A.(AilEident sym)  (* TODO: Check. Need to do more work if this is only a CN var *)
      )
    (* 
    | CNExpr_list es_ -> !^ "[...]" (* Currently unused *)
    *)
    | CNExpr_memberof (e, xs) -> A.(AilEmemberof (mk_expr (cn_to_ail_expr ~const_prop e), xs))
    (* 
    | CNExpr_record es -> failwith "TODO"
    | CNExpr_memberupdates (e, _updates) -> !^ "{_ with ...}"
    | CNExpr_arrayindexupdates (e, _updates) -> !^ "_ [ _ = _ ...]"
    *)

    (* TODO: binary operations on structs (esp. equality) *)
    | CNExpr_binop (bop, x, y) -> 
      A.AilEbinary (mk_expr (cn_to_ail_expr ~const_prop x), cn_to_ail_binop bop, mk_expr (cn_to_ail_expr ~const_prop y))  
    
    | CNExpr_sizeof ct -> A.AilEsizeof (empty_qualifiers, ct) 
    
    | CNExpr_offsetof (tag, member) -> 
      A.(AilEoffsetof (C.(Ctype ([], Struct tag)), member))

    (* TODO: Test *)
    | CNExpr_membershift (e, _, member) ->
      A.(AilEunary (Address, mk_expr (AilEmemberofptr (mk_expr (cn_to_ail_expr ~const_prop e), member))))

    | CNExpr_cast (bt, expr) -> A.(AilEcast (empty_qualifiers, C.Ctype ([], cn_to_ail_base_type bt) , (mk_expr (cn_to_ail_expr ~const_prop expr))))
    
    | CNExpr_call (sym, exprs) -> 
      let ail_exprs = List.map (fun e -> mk_expr (cn_to_ail_expr ~const_prop e)) exprs in
      let f = (mk_expr A.(AilEident sym)) in
      A.AilEcall (f, ail_exprs)
    
    (*
    | CNExpr_cons (c_nm, exprs) -> !^ "(" ^^ Sym.pp c_nm ^^^ !^ "{...})"
    *)

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
      let ail_exprs = List.map (fun cn_const -> cn_to_ail_expr ~const_prop:(Some (sym, cn_const)) e) cn_consts in
      (match ail_exprs with
        | (ail_expr1 :: ail_exprs_rest) ->  List.fold_left (fun ae1 ae2 -> A.(AilEbinary (mk_expr ae1, And, mk_expr ae2))) ail_expr1 ail_exprs_rest
        | [] -> failwith "Cannot have empty expression in CN each expression")
  
    (* TODO: Implement. AilSswitch is a statement_ not an expression *)
    (* Could try making everything a statement via AilSexpr *)
    (* TODO: Add proper error messages for cases handled differently (exprs which are statements in C) *)
    (* | CNExpr_match (e, es) -> failwith "TODO"  *)

  
    (* TODO: Might want to consider destination-passing style for if-then-else too (if ternary expressions turn out to look too complicated) *)
    | CNExpr_ite (e1, e2, e3) -> 
      let ail_e1 = cn_to_ail_expr ~const_prop e1 in
      let ail_e2 = cn_to_ail_expr ~const_prop e2 in
      let ail_e3 = cn_to_ail_expr ~const_prop e3 in
      A.AilEcond (mk_expr ail_e1, Some (mk_expr ail_e2), mk_expr ail_e3)
    
    (* 
    | CNExpr_good (ty, e) -> !^ "(good (_, _))" 
    *)

    | CNExpr_deref e -> A.(AilEunary (Indirection, mk_expr (cn_to_ail_expr ~const_prop e)))

    | CNExpr_unchanged e -> 
      let e_at_start = CNExpr(loc, CNExpr_at_env (e, start_evaluation_scope)) in
      cn_to_ail_expr ~const_prop (CNExpr (loc, CNExpr_binop (CN_equal, e, e_at_start)))
  
    | CNExpr_at_env (e, es) as cn_expr -> cn_to_ail_expr_at_env cn_expr 

    | CNExpr_not e -> A.(AilEunary (Bnot, mk_expr (cn_to_ail_expr ~const_prop e))) 
    | _ -> failwith "TODO"


type 'a ail_datatype = {
  structs: (C.union_tag * (Cerb_location.t * CF.Annot.attributes * C.tag_definition)) list;
  decls: (C.union_tag * A.declaration) list;
  stats: 'a A.statement list;
}


let cn_to_ail_datatype (cn_datatype : cn_datatype) =
  let cntype_sym = Sym.fresh_pretty "cntype" in
  let cntype_struct = (cntype_sym, (Cerb_location.unknown, empty_attributes, C.(StructDef ([], None)))) in
  let generate_tag_definition dt_members = 
    let identifiers = List.map fst dt_members in
    let create_member ?(ctype_=C.(Pointer (empty_qualifiers, Ctype ([], Void)))) id =
      (id, (empty_attributes, None, empty_qualifiers, mk_ctype ctype_))
    in
    (* TODO: Check if something called tag already exists *)
    let cntype_pointer = C.(Pointer (empty_qualifiers, mk_ctype (Struct cntype_sym))) in
    let extra_members = [
      (create_member ~ctype_:C.(Basic (Integer (Signed Int_))) (Id.id "tag"));
      (create_member ~ctype_:cntype_pointer (Id.id "cntype"))] in
    let members = List.map create_member (identifiers) in
    C.(StructDef (extra_members @ members, None))
  in
  let generate_struct_definition (constructor, members) = (constructor, (Cerb_location.unknown, empty_attributes, generate_tag_definition members))
  in
  let structs = List.map generate_struct_definition cn_datatype.cn_dt_cases in
  let structs = cntype_struct :: structs in
  let generate_constructor_sym constructor =  
    let doc = 
    CF.Pp_ail.pp_id ~executable_spec:true constructor ^^ (!^ "_tag") in 
    let str = 
    CF.Pp_utils.to_plain_string doc in 
    Sym.fresh_pretty str
  in
  let rec generate_stats cases count =
    (match cases with 
      | [] -> []
      | (constructor, _) :: cs -> 
        let const = mk_expr (A.(AilEconst (ConstantInteger (IConstant (Z.of_int count, Decimal, None))))) in
        let constructor_sym = generate_constructor_sym constructor in
        (constructor_sym, Some const) :: (generate_stats cs (count + 1))
  )
  in
  (* TODO: Make const? *)
  let decl_object = A.(Decl_object ((Automatic, false), None, empty_qualifiers, mk_ctype C.(Basic (Integer (Signed Int_))))) in
  let stats = generate_stats cn_datatype.cn_dt_cases 0 in
  let decls = List.map (fun (sym, _) -> (sym, decl_object)) stats in
  let stats = List.map (fun d -> mk_stmt (A.AilSdeclaration [d])) stats in
  {structs = structs; decls = decls; stats = stats}


let is_cn_expr_simple (CNExpr (_, expr_)) = 
  match expr_ with 
    | CNExpr_match _ -> false
    | _ -> true


let cn_to_ail_assertion = function
  | CN_assert_exp e_ -> 
    if (is_cn_expr_simple e_) then
      let ail_expr = A.(AilEassert (mk_expr (cn_to_ail_expr e_))) in 
      [mk_stmt A.(AilSexpr (mk_expr ail_expr))]
    else
      failwith "TODO"
  | CN_assert_qexp (ident, bTy, e1, e2) -> failwith "TODO"


let cn_to_ail_condition cn_condition type_map = 
  match cn_condition with
  | CN_cletResource (loc, name, resource) -> ([A.AilSskip], None) (* TODO *)
  | CN_cletExpr (_, name, expr) -> 
    let ail_expr = cn_to_ail_expr expr in
    let sfb_type = SymTable.find type_map name in
    let basetype = SurfaceBaseTypes.to_basetype sfb_type in
    let cn_basetype = bt_to_cn_base_type basetype in
    let ctype = cn_to_ail_base_type cn_basetype in
    ([A.(AilSdeclaration [(name, Some (mk_expr ail_expr))])], Some (mk_ctype ctype))
  | CN_cconstr (loc, constr) -> 
    let ail_constr = cn_to_ail_assertion constr in
    let ail_stats_ = List.map rm_stmt ail_constr in
    (ail_stats_, None)
