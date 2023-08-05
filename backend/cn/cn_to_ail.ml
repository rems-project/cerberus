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

module ConstructorPattern = struct
  type t = C.union_tag 
  let compare (x : t) y = Sym.compare_sym x y
end

module PatternMap = Map.Make(ConstructorPattern)

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

let prefix : type a. a dest -> CF.GenTypes.genTypeCategory A.statement_ list -> a -> a = 
  fun d s1 u -> 
    match d, u with 
    | Assert, s2 -> s1 @ s2
    | Return, s2 -> s1 @ s2
    | AssignVar _, s2 -> s1 @ s2
    | PassBack, (s2, e) -> (s1 @ s2, e)

let create_id_from_sym ?(lowercase=false) sym =
  let str = Sym.pp_string sym in 
  let str = if lowercase then String.lowercase_ascii str else str in
  Id.id str

let create_sym_from_id id = 
  Sym.fresh_pretty (Id.pp_string id)


let generate_sym_with_suffix ?(suffix="_tag") ?(uppercase=false) ?(lowercase=false) constructor =  
  let doc = 
  CF.Pp_ail.pp_id ~executable_spec:true constructor ^^ (!^ suffix) in 
  let str = 
  CF.Pp_utils.to_plain_string doc in 
  let str = if uppercase then String.uppercase_ascii str else str in
  let str = if lowercase then String.lowercase_ascii str else str in
  (* Printf.printf "%s\n" str; *)
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
      (* exprs currently unused *)
      let tag_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true c_nm in
      (* let _generate_assign_stat (id, expr) = 
        let _s, rhs_ail_expr = cn_to_ail_expr_aux const_prop dts expr PassBack in
        let sym = create_sym_from_id id in
        let ail_expr = A.(AilEassign (mk_expr (AilEident sym), mk_expr rhs_ail_expr)) in
        A.(AilSexpr (mk_expr (ail_expr)))
      in
      (match exprs with 
        | (i, _) :: (i', _) :: _ -> 
            Printf.printf "%s\n%s\n" (Id.pp_string i) (Id.pp_string i') 
        | _ -> ()
      ); *)
      (* Treating enum value as variable name *)
      dest d ([], AilEident tag_sym)   

    (* Should only be integer range *)
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
  
    | CNExpr_match (e, es) ->
      
      (* PATTERN COMPILER *)

      (* let create_binding sym ctype =  *)
        (* A.(sym, ((Location_ocaml.unknown, Automatic, false), None, empty_qualifiers, ctype)) *)
      (* in *)


      let simplify_leading_variable cn_expr_ (ps, e) =
        match ps with 
          (* CNExpr_const CNConst_unit is a hacky representation for wildcard pattern *)
          | CNPat (loc, CNPat_sym sym) :: ps' -> 
            (* let binding = create_binding sym' (mk_ctype (cn_to_ail_base_type tp)) in *)
            CNPat (loc, CNPat_wild) :: ps', mk_cn_expr (CNExpr_let (sym, mk_cn_expr cn_expr_, e))
          | p :: ps' -> (p :: ps', e)
          | [] -> assert false
      in

      let leading_wildcard (ps, _) =
        match ps with
          | CNPat (loc, CNPat_wild) :: ps' -> true
          | _ :: ps' -> false
          | [] -> failwith "Empty patterns not allowed"
      in

      let rec append_to_all elem bindings m = 
        match bindings with 
          | [] -> m
          | b :: bs ->
            let curr = PatternMap.find b m in
            let m' = PatternMap.remove b m in
            let m' = PatternMap.add b (curr @ [elem]) m' in 
            append_to_all elem bs m'
      in 

      (* Used when no type information available (top-level call to translate) *)
      let rec _split_into_groups cases m =
          match cases with
            | [] -> m
            | ((lhs, rhs) as case) :: cases' -> 
              let new_m = (match lhs with 
                | CNPat (_, CNPat_constructor (c_nm, _)) :: _ -> (* Check if constructor already exists in split *)
                  if (PatternMap.mem c_nm m) then 
                    let curr = PatternMap.find c_nm m in
                    let m' = PatternMap.remove c_nm m in
                    PatternMap.add c_nm (curr @ [case]) m'
                  else
                    PatternMap.add c_nm [case] m
                | CNPat (_, CNPat_sym _) :: _ (* This case shouldn't occur because of call to simplify_leading_variable *)
                | CNPat (_, CNPat_wild) :: _ ->
                    (* Everything should be a wildcard pattern after functions that have been called *)
                    (* Above pattern maybe shouldn't exist? *)
                    let (keys, vals) = List.split (PatternMap.bindings m) in
                     append_to_all case keys m
                | _ -> failwith "No other cases allowed on LHS of pattern match")
              in
              _split_into_groups cases' new_m
      in

      let _expand_record ids (ps, e) =
        match ps with
          | CNExpr_const CNConst_unit :: ps' ->
            let ps'' = List.map (fun _ -> CNExpr_const CNConst_unit) ids in
            (ps'' @ ps', e)
          | CNExpr_record members :: ps' ->
            if List.for_all2 (fun (id, m) id' -> Id.equal id id') members ids then
              let ps'' = List.map (fun (id, m) -> rm_cn_expr m) members in 
              (ps'' @ ps', e)
            else 
              failwith "Fields in pattern not the same as fields in type"
          | _ :: _ -> failwith "Non-record pattern"
          | [] -> assert false
      in  

      let expand_datatype c (ps, e) = 
        match ps with 
        | CNPat (loc, CNPat_wild) :: ps' -> Some (CNPat (loc, CNPat_wild) :: ps', e)
        | CNPat (loc, (CNPat_constructor (c_nm, members))) :: ps' ->
          if Sym.equal_sym c c_nm then
            let member_patterns = List.map (fun (id, p) -> p) members in
            Some (member_patterns @ ps', e)
          else
            None
        | _ :: _ -> failwith "Non-sum pattern" 
        | [] -> assert false 
      in 

      let transform_switch_expr e_
        = A.(AilEmemberofptr (mk_expr e_, Id.id "tag"))
      in

      (* TODO: Incorporate destination passing recursively into this. Might need PassBack throughout, like in cn_to_ail_expr_aux function *)
      (* TODO: Add map of datatype constructors names to counts (to avoid repetition of variable names) *)
      (* Matrix algorithm for pattern compilation *)
      let rec translate : int -> (((C.union_tag, C.ctype) cn_expr_) * _ Cn.cn_base_type) list -> ((C.union_tag cn_pat) list * (C.union_tag, C.ctype) cn_expr) list -> (A.bindings list * (_ A.statement_) list) =
        fun count vars cases -> 
          match vars with 
            | [] ->
              (match cases with 
              | ([], e) :: rest -> 
                (match d with 
                | Assert -> 
                  let rhs = cn_to_ail_expr_aux const_prop dts e Assert in
                  ([], rhs)
                | Return -> 
                  let rhs = cn_to_ail_expr_aux const_prop dts e Return in
                  ([], rhs)
                | AssignVar x -> failwith "TODO"
                | PassBack -> failwith "TODO")
              | [] -> failwith "Incomplete pattern match"
              | ((_::_), e) :: rest -> assert false)

            | (v, tp) :: vs -> 
              
              let cases = List.map (simplify_leading_variable v) cases in

              if List.for_all leading_wildcard cases then
                (Printf.printf "All leading patterns are wildcards\n";
                let cases = List.map (fun (ps, e) -> (List.tl ps, e)) cases in
                if (List.length cases != 0) then
                Printf.printf "Length of patterns: %d\n" (List.length (fst (List.hd cases)));
                let (bindings', stats') = translate count vs cases in 
                ([], stats'))
              else
                match tp with
                  | CN_datatype sym -> 
                      Printf.printf "Inside datatype case. Sym = %s\n" (Sym.pp_string sym);

                      let cn_dt = List.filter (fun dt -> String.equal (Sym.pp_string sym) (Sym.pp_string dt.cn_dt_name)) dts in 
                      (match cn_dt with 
                        | [] -> failwith "Datatype not found"
                        | dt :: _ ->
                          let (s1, e1) = cn_to_ail_expr_aux const_prop dts (mk_cn_expr v) PassBack in
                          let build_case (constr_sym, members_with_types) = 
                            let cases' = List.filter_map (expand_datatype constr_sym) cases in 
                            let record_tp = CN_record members_with_types in
                            Printf.printf "Number of members in datatype: %d\n" (List.length members_with_types);
                            let suffix = "_" ^ (string_of_int count) in
                            let lc_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true constr_sym in 
                            let count_sym = generate_sym_with_suffix ~suffix ~lowercase:true constr_sym in 
                            let rhs_memberof_ptr = A.(AilEmemberofptr (mk_expr e1, Id.id "u")) in (* TODO: Remove hack *)
                            let rhs_memberof = A.(AilEmemberof (mk_expr rhs_memberof_ptr, create_id_from_sym lc_sym)) in
                            let constructor_var_assign = mk_stmt A.(AilSdeclaration [(count_sym, Some (mk_expr rhs_memberof))]) in
                            let (_bindings, member_stats) = translate (count + 1) ((CNExpr_var count_sym, record_tp) :: vs) cases' in
                            (* TODO: Add real bindings instead of [] *)
                            let stat_block = A.AilSblock ([], constructor_var_assign :: (List.map mk_stmt member_stats)) in
                            let tag_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true constr_sym in
                            let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, Sym.pp_string tag_sym); attr_args = []} in
                            let ail_case = A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt stat_block)) in
                            let ail_case_stmt = A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case)) in
                            ail_case_stmt
                          in 
                          let e1_transformed = transform_switch_expr e1 in
                          let ail_case_stmts = List.map build_case dt.cn_dt_cases in
                          let switch = A.(AilSswitch (mk_expr e1_transformed, mk_stmt (AilSblock ([], ail_case_stmts)))) in
                          ([], s1 @ [switch])
                      )
                  | _ -> 
                    (* Cannot have non-variable, non-wildcard pattern besides struct *)
                    failwith "Unexpected pattern"
      in

      let translate_real : type a. (((C.union_tag, C.ctype) cn_expr_) * _ Cn.cn_base_type) list -> ((C.union_tag) cn_pat list * (C.union_tag, C.ctype) cn_expr) list -> a dest -> a =
        fun vars cases d ->
          let (bs, ss) = translate 1 vars cases in
          match d with 
            | Assert -> ss
            | Return -> ss
            | AssignVar x -> failwith "TODO"
            | PassBack -> failwith "TODO"
      in 

      (* TODO: Make sure recursive pattern matches work now that we are using cnexprs and not vars  *)
      
      (* Hack before switching over to CN's internal AST *)
      let tree_sym = Sym.fresh_pretty "tree" in
      let ps = List.map (fun (lhs, rhs) -> ([lhs], rhs)) es in
      translate_real [(rm_cn_expr e, CN_datatype tree_sym)] ps d

  
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
      let s1, e1 = cn_to_ail_expr_aux const_prop dts e PassBack in
      let ail_assign = A.(AilSdeclaration [(s, Some (mk_expr e1))]) in
      prefix d (s1 @ [ail_assign]) (cn_to_ail_expr_aux const_prop dts body d)

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
    let ail_dt_members = List.map (fun (cn_type, id) -> (cn_to_ail_base_type cn_type, id)) dt_members in
    (* TODO: Check if something called tag already exists *)
    let members = List.map create_member ail_dt_members in
    C.(StructDef (members, None))
  in
  let generate_struct_definition (constructor, members) = 
    let lc_constructor_str = String.lowercase_ascii (Sym.pp_string constructor) in
    let lc_constructor = Sym.fresh_pretty lc_constructor_str in
    (lc_constructor, (Cerb_location.unknown, empty_attributes, generate_tag_definition members))
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
  let union_sym = generate_sym_with_suffix ~suffix:"_union" cn_datatype.cn_dt_name in
  let union_def_members = List.map (fun sym -> 
    let lc_sym = Sym.fresh_pretty (String.lowercase_ascii (Sym.pp_string sym)) in
    create_member (C.(Struct lc_sym), create_id_from_sym ~lowercase:true sym)) constructor_syms in
  let union_def = C.(UnionDef union_def_members) in
  let union_member = create_member (C.(Union union_sym), Id.id "u") in

  let structs = structs @ [(union_sym, (Cerb_location.unknown, empty_attributes, union_def)); (cn_datatype.cn_dt_name, (Cerb_location.unknown, empty_attributes, C.(StructDef ((extra_members (C.(Basic (Integer (Enum enum_sym))))) @ [union_member], None))))] in
  {structs = enum :: structs; decls = []; stats = []}



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
  let params = List.map (fun (cn_bt, cn_nm) -> (mk_ctype (cn_to_ail_base_type cn_bt), cn_nm)) cn_function.cn_func_args in
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
