module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
open CF.Cn
open Compile
open Executable_spec_utils
open PPrint
open Mucore
module A=CF.AilSyntax
module C=CF.Ctype
module BT=BaseTypes
module T=Terms
module LRT=LogicalReturnTypes
module LAT=LogicalArgumentTypes

let rec cn_base_type_to_bt = function
  | CN_unit -> BT.Unit
  | CN_bool -> BT.Bool  
  | CN_integer -> BT.Integer
  | CN_bits (sign, size) ->
      BT.Bits ((match sign with CN_unsigned -> BT.Unsigned | CN_signed -> BT.Signed), size)
  | CN_real -> BT.Real
  | CN_loc -> BT.Loc
  | CN_alloc_id -> BT.Alloc_id
  | CN_struct tag -> BT.Struct tag
  | CN_datatype tag -> BT.Datatype tag
  | CN_record ms -> 
    let ms' = List.map (fun (bt, id) -> (id, cn_base_type_to_bt bt)) ms in
    BT.Record ms'
  | CN_map (type1, type2) -> BT.Map (cn_base_type_to_bt type1, cn_base_type_to_bt type2)
  | CN_list typ -> cn_base_type_to_bt typ
  | CN_tuple ts -> BT.Tuple (List.map cn_base_type_to_bt ts)
  | CN_set typ -> cn_base_type_to_bt typ
  | CN_user_type_name _ -> failwith "TODO"
  | CN_c_typedef_name _ -> failwith "TODO"
  

module MembersKey = struct
  type t = (symbol cn_base_type * Id.t) list
  let rec compare (ms : t) ms' =
    match (ms, ms') with 
      | ([], []) -> 0
      | (_, []) -> 1
      | ([], _) -> -1
      | ((_, id) :: ms, (_, id') :: ms') -> 
        let c = String.compare (Id.s id) (Id.s id') in
        if c == 0 then
          0
        else
          compare ms ms'

    
end


let members_equal ms ms' = 
  let (cn_bts, ids) = List.split ms in
  let (cn_bts', ids') = List.split ms' in
  let ctypes_eq = List.map2 (fun cn_bt cn_bt'->
    let bt = cn_base_type_to_bt cn_bt in
    let bt' = cn_base_type_to_bt cn_bt' in
    BT.equal bt bt') cn_bts cn_bts' in
  let ids_eq = List.map2 Id.equal ids ids' in
  (List.fold_left (&&) true ctypes_eq) && (List.fold_left (&&) true ids_eq)

module SymKey = struct
  type t = C.union_tag 
  let compare (x : t) y = Sym.compare_sym x y
end


module RecordMap = Map.Make(MembersKey)

let records = ref RecordMap.empty

let generic_cn_dt_sym = Sym.fresh_pretty "cn_datatype"

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

let create_binding sym ctype_ = 
  A.(sym, ((Cerb_location.unknown, Automatic, false), None, empty_qualifiers, mk_ctype ctype_))


  

let rec bt_to_cn_base_type = function
| BT.Unit -> CN_unit
| BT.Bool -> CN_bool
| BT.Integer -> CN_integer
| BT.Bits _ -> failwith "TODO"
| BT.Real -> CN_real
| BT.Alloc_id  -> failwith "TODO BT.Alloc_id"
| BT.CType -> failwith "TODO BT.Ctype"
| BT.Loc -> CN_loc
| BT.Struct tag -> CN_struct tag
| BT.Datatype tag -> CN_datatype tag
| BT.Record member_types -> 
  let ms = List.map (fun (id, bt) -> (bt_to_cn_base_type bt, id)) member_types in
  CN_record ms
| BT.Map (bt1, bt2) -> CN_map (bt_to_cn_base_type bt1, bt_to_cn_base_type bt2)
| BT.List bt -> CN_list (bt_to_cn_base_type bt)
| BT.Tuple bts -> CN_tuple (List.map bt_to_cn_base_type bts)
| BT.Set bt -> CN_set (bt_to_cn_base_type bt)



(* TODO: Complete *)
let rec cn_to_ail_base_type ?(pred_sym=None) = 
  let generate_ail_array bt = C.(Array (Ctype ([], cn_to_ail_base_type bt), None)) in 
  function
  | CN_unit -> C.Void
  | CN_bool -> C.(Basic (Integer Bool))
  | CN_integer -> C.(Basic (Integer (Signed Long))) (* TODO: Discuss integers *)
  (* | CN_real -> failwith "TODO" *)
  | CN_loc -> C.(Pointer (empty_qualifiers, Ctype ([], Void))) (* Casting all CN pointers to void star *)
  | CN_struct sym -> C.(Struct sym)
  | CN_record members -> 
    let map_bindings = RecordMap.bindings !records in
    let eq_members_bindings = List.filter (fun (k, v) -> members_equal k members) map_bindings in
    let sym = (
    match pred_sym with
      | Some sym' -> 
        let sym'' = generate_sym_with_suffix ~suffix:"_record" sym' in
        records := RecordMap.add members sym'' !records;
        sym''
      | None ->   
        match eq_members_bindings with 
        | [] -> 
          (* First time reaching record of this type - add to map *)
          let count = RecordMap.cardinal !records in
          let sym' = Sym.fresh_pretty ("record_" ^ (string_of_int count)) in
          records := RecordMap.add members sym' !records;
          sym'
        | (_, sym') :: _ -> sym')
    in
    C.(Pointer (empty_qualifiers, mk_ctype (Struct sym)))

  (* Every struct is converted into a struct pointer *)
  | CN_datatype sym -> C.(Pointer (empty_qualifiers, Ctype ([], Struct sym)))
  (* TODO: Implement maps properly *)
  | CN_map (_, cn_bt) -> generate_ail_array cn_bt
  | CN_list bt -> generate_ail_array bt (* TODO: What is the optional second pair element for? Have just put None for now *)
  (* | CN_tuple of list (cn_base_type 'a) *)
  | CN_set bt -> generate_ail_array bt
  | _ -> failwith "TODO cn_to_ail_base_type"

let bt_to_ail_ctype ?(pred_sym=None) t = cn_to_ail_base_type ~pred_sym (bt_to_cn_base_type t)

(* TODO: Finish *)
let cn_to_ail_binop_internal = function
  | Terms.And -> (A.And, None)
  | Or -> (A.Or, None)
  (* | Impl *)
  | Add -> (A.(Arithmetic Add), None)
  | Sub -> (A.(Arithmetic Sub), None)
  | Mul 
  | MulNoSMT -> (A.(Arithmetic Mul), None)
  | Div 
  | DivNoSMT -> (A.(Arithmetic Div), None)
  | Exp
  | ExpNoSMT -> (A.And, Some "pow")
  (* | Rem
  | RemNoSMT *)
  | Mod
  | ModNoSMT -> (A.(Arithmetic Mod), None)
  | XORNoSMT -> (A.(Arithmetic Bxor), None)
  | BWAndNoSMT -> (A.(Arithmetic Band), None)
  | BWOrNoSMT -> (A.(Arithmetic Bor), None)
  | LT -> (A.Lt, None)
  | LE -> (A.Le, None)
  | Min -> (A.And, Some "min")
  | Max -> (A.And, Some "max")
  | EQ -> (A.Eq, None)
  | _ -> (A.And, None) (* TODO: Change *)
  (* | LTPointer
  | LEPointer
  | SetUnion
  | SetIntersection
  | SetDifference
  | SetMember
  | Subset *)

(* Assume a specific shape, where sym appears on the RHS (i.e. in e2) *)
let rearrange_start_inequality sym e1 e2 = 
  match (rm_expr e2) with 
    | A.(AilEbinary ((A.AnnotatedExpression (_, _, _, AilEident sym1) as expr1), binop, (A.AnnotatedExpression (_, _, _, AilEident sym2) as expr2))) ->
        (if String.equal (Sym.pp_string sym) (Sym.pp_string sym1) then
          let inverse_binop = match binop with 
            | A.(Arithmetic Add) -> A.(Arithmetic Sub)
            | A.(Arithmetic Sub) -> A.(Arithmetic Add)
            | _ -> failwith "Other binops not supported"
          in
          A.(AilEbinary (e1, inverse_binop, expr2))
        else 
          (if String.equal (Sym.pp_string sym) (Sym.pp_string sym2) then 
            match binop with 
              | A.(Arithmetic Add) -> A.(AilEbinary (e1, A.(Arithmetic Sub), expr1))
              | A.(Arithmetic Sub) -> failwith "Minus not supported"
              | _ -> failwith "Other binops not supported"
          else 
            failwith "Not of correct form"
          )
        )
    | _ -> failwith "TODO"


let generate_start_expr start_cond sym =
  let (start_expr, binop) = 
    match start_cond with
      | A.(AilEbinary (expr1, binop, A.AnnotatedExpression (_, _, _, AilEident sym'))) ->
          (if String.equal (Sym.pp_string sym) (Sym.pp_string sym') then
            (expr1, binop)
          else
            failwith "Not of correct form (unlikely case - i's not matching)")
      | A.(AilEbinary (expr1, binop, expr2)) ->
          (mk_expr (rearrange_start_inequality sym expr1 expr2), binop)
      | _ -> failwith "Not of correct form: more complicated RHS of binexpr than just i"
  in
  match binop with 
    | A.Le -> 
      start_expr
    | A.Lt ->
      let one = A.AilEconst (ConstantInteger (IConstant (Z.of_int 1, Decimal, None))) in
      mk_expr (A.(AilEbinary (start_expr, Arithmetic Add, mk_expr one)))
    | _ -> failwith "Not of correct form: not Le or Lt"

    let rec get_leftmost_and_expr = function
    | A.(AilEbinary (lhs, And, rhs)) -> get_leftmost_and_expr (rm_expr lhs)
    | lhs -> lhs
  

  let rec get_rest_of_expr_r = function 
    | A.(AilEbinary (lhs, And, rhs)) ->
      let r = get_rest_of_expr_r (rm_expr lhs) in
      (match r with
        | A.(AilEconst (ConstantInteger (IConstant _))) -> rm_expr rhs
        | _ -> A.(AilEbinary (mk_expr r, And, rhs)))
    | lhs -> A.AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int true), Decimal, Some B)))
  

let gen_bool_while_loop sym start_expr while_cond (bs, ss, e) = 
  let b = Sym.fresh () in
  let b_ident = A.(AilEident b) in
  let b_binding = create_binding b C.(Basic (Integer Bool)) in
  let true_const = A.AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int true), Decimal, Some B))) in
  let b_decl = A.(AilSdeclaration [(b, Some (mk_expr true_const))]) in

  let incr_var = A.(AilEident sym) in
  let incr_var_binding = create_binding sym C.(Basic (Integer (Signed Int_))) in
  let start_decl = A.(AilSdeclaration [(sym, Some (mk_expr start_expr))]) in

  let rhs_and_expr_ = A.(AilEbinary (mk_expr b_ident, And, e)) in
  let b_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr b_ident, mk_expr rhs_and_expr_)))) in
  let incr_stat = A.(AilSexpr (mk_expr (AilEunary (PostfixIncr, mk_expr incr_var)))) in
  let while_loop = A.(AilSwhile (mk_expr while_cond, mk_stmt (AilSblock (bs, List.map mk_stmt (ss @ [b_assign; incr_stat]))), 0)) in

  let block = A.(AilSblock ([incr_var_binding], List.map mk_stmt [start_decl; while_loop])) in
  ([b_binding], [b_decl; block], mk_expr b_ident)


let rec cn_to_ail_const_internal = function
  | Terms.Z z -> A.AilEconst (ConstantInteger (IConstant (z, Decimal, None)))
  | Q q -> A.AilEconst (ConstantFloating (Q.to_string q, None))
  | Pointer z -> 
    Printf.printf "In Pointer case; const\n";
    A.AilEunary (Address, mk_expr (cn_to_ail_const_internal (Terms.Z z.addr)))
  | Bool b -> A.AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int b), Decimal, Some B)))
  | Unit -> A.AilEconst (ConstantIndeterminate C.(Ctype ([], Void)))
  | Null -> A.AilEconst (ConstantNull)
  (* TODO *)
  | CType_const ct -> failwith "TODO: CType_Const"
  (* | Default of BaseTypes.t  *)
  | _ -> failwith "TODO cn_to_ail_const_internal"

type 'a dest =
| Assert : (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list) dest
| Return : (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list) dest 
| AssignVar : C.union_tag -> (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list) dest
| PassBack : (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression) dest

let dest : type a. a dest -> A.bindings * CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression -> a = 
  fun d (b, s, e) -> 
    match d with
    | Assert -> 
      let assert_stmt = A.(AilSexpr (mk_expr (AilEassert e))) in
      (b, s @ [assert_stmt])
    | Return ->
      let return_stmt = A.(AilSreturn e) in
      (b, s @ [return_stmt])
    | AssignVar x -> 
      let assign_stmt = A.(AilSdeclaration [(x, Some e)]) in
      (b, s @ [assign_stmt])
    | PassBack -> (b, s, e)

let prefix : type a. a dest -> (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list) -> a -> a = 
  fun d (b1, s1) u -> 
    match d, u with 
    | Assert, (b2, s2) -> (b1 @ b2, s1 @ s2)
    | Return, (b2, s2) -> (b1 @ b2, s1 @ s2)
    | AssignVar _, (b2, s2) -> (b1 @ b2, s1 @ s2)
    | PassBack, (b2, s2, e) -> (b1 @ b2, s1 @ s2, e)

let empty_for_dest : type a. a dest -> a = 
  fun d ->
    match d with 
      | Assert -> ([], [empty_ail_stmt])
      | Return -> ([], [empty_ail_stmt])
      | AssignVar _ -> ([], [empty_ail_stmt])
      | PassBack -> ([], [empty_ail_stmt], mk_expr empty_ail_expr)





(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
(* TODO: Use mu_datatypes from Mucore program instead of cn_datatypes *)
let rec cn_to_ail_expr_aux_internal 
: type a. (_ option) -> (_ option) -> (_ Cn.cn_datatype) list -> IT.t -> a dest -> a
= fun const_prop pred_name dts (IT (term_, basetype)) d ->
  (* let _cn_to_ail_expr_aux_internal_at_env : type a. _ cn_expr -> string -> a dest -> a
  = (fun e es d ->
      (match es with
        | start_evaluation_scope -> 
          (* let Symbol (digest, nat, _) = CF.Symbol.fresh () in *)
          (* TODO: Make general *)
          let s, ail_expr = cn_to_ail_expr_aux_internal const_prop dts e PassBack in
          let e_cur_nm =
          match ail_expr with
            | A.(AilEident sym) -> CF.Pp_symbol.to_string_pretty sym (* Should only be AilEident sym - function arguments only *)
            | _ -> failwith "Incorrect type of Ail expression"
          in
          let e_old_nm = e_cur_nm ^ "_old" in
          let sym_old = CF.Symbol.Symbol ("", 0, SD_CN_Id e_old_nm) in
          dest d (s, A.(AilEident sym_old))
          ))
  in *)
  (* let typ = cn_to_ail_base_type (bt_to_cn_base_type basetype) in
  let doc = CF.Pp_ail.pp_ctype ~executable_spec:true empty_qualifiers (mk_ctype typ) in
  Printf.printf "C type: %s\n" (CF.Pp_utils.to_plain_pretty_string doc); *)
  match term_ with
  | Const const ->
    let ail_expr_ = cn_to_ail_const_internal const in
    dest d ([], [], mk_expr ail_expr_)

  | Sym sym ->
    let sym = 
      if (String.equal (Sym.pp_string sym) "return") then
        Sym.fresh_pretty "__cn_ret"
      else 
        sym 
    in
    let ail_expr_ = 
      (match const_prop with
        | Some (sym2, cn_const) ->
            if CF.Symbol.equal_sym sym sym2 then
              cn_to_ail_const_internal cn_const
            else
              A.(AilEident sym)
        | None -> A.(AilEident sym)  (* TODO: Check. Need to do more work if this is only a CN var *)
      )
      in
      dest d ([], [], mk_expr ail_expr_)

  | Binop (bop, t1, t2) ->
    let b1, s1, e1 = cn_to_ail_expr_aux_internal const_prop pred_name dts t1 PassBack in
    let b2, s2, e2 = cn_to_ail_expr_aux_internal const_prop pred_name dts t2 PassBack in
    let (ail_bop, annot) = cn_to_ail_binop_internal bop in
    let strs = match annot with 
      | Some str -> [str]
      | None -> []
    in
    let ail_expr_ = A.AilEbinary (e1, ail_bop, e2) in 
    dest d (b1 @ b2, s1 @ s2, mk_expr ~strs ail_expr_) 

  | Not t -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in
    let ail_expr_ = A.(AilEunary (Bnot, e)) in 
    dest d (b, s, mk_expr ail_expr_)

  | ITE (t1, t2, t3) -> 
    let b1, s1, e1 = cn_to_ail_expr_aux_internal const_prop pred_name dts t1 PassBack in
    let b2, s2, e2 = cn_to_ail_expr_aux_internal const_prop pred_name dts t2 PassBack in
    let b3, s3, e3 = cn_to_ail_expr_aux_internal const_prop pred_name dts t3 PassBack in
    let ail_expr_ = A.AilEcond (e1, Some e2, e3) in
    dest d (b1 @ b2 @ b3, s1 @ s2 @ s3, mk_expr ail_expr_)

  | EachI ((r_start, (sym, bt), r_end), t) -> 

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

    let mk_int_const n = 
      A.AilEconst (ConstantInteger (IConstant (Z.of_int n, Decimal, None)))
    in

    let incr_var = A.(AilEident sym) in
    let start_int_const = mk_int_const r_start in
    let end_int_const = mk_int_const r_end in
    let while_cond = A.(AilEbinary (mk_expr incr_var, Lt, mk_expr end_int_const)) in
    let translated_t = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in

    let (bs, ss, e) = gen_bool_while_loop sym start_int_const while_cond translated_t in
    dest d (bs, ss, e)

  (* add Z3's Distinct for separation facts  *)
  | Tuple ts -> failwith "TODO1"
  | NthTuple (i, t) -> failwith "TODO2"
  | Struct (tag, ms) -> failwith "TODO3"

  | RecordMember (t, m) ->
    (* Currently assuming records only exist  *)
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in
    let ail_expr_ = match pred_name with
      | Some sym -> A.(AilEmemberofptr (e, m))
      | None -> A.(AilEmemberof (e, m))
    in
    dest d (b, s, mk_expr ail_expr_)

  | StructMember (t, m) -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in
    let ail_expr_ = A.(AilEmemberof (e, m)) in
    dest d (b, s, mk_expr ail_expr_)

  | StructUpdate ((struct_term, m), new_val) ->
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts struct_term PassBack in
    let (b2, s2, e2) = cn_to_ail_expr_aux_internal const_prop pred_name dts new_val PassBack in
    let ail_memberof = A.(AilEmemberof (e1, m)) in
    let ail_assign = A.(AilSexpr (mk_expr (AilEassign ((mk_expr ail_memberof, e2))))) in
    dest d (b1 @ b2, s1 @ s2 @ [ail_assign], e1)

    (* Allocation *)
  | Record ms -> 
    (* Could either be (1) standalone record or (2) part of datatype. Case (2) may not exist soon *)
    (* Might need to pass records around like datatypes *)

    Printf.printf "Entered record case\n";

    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in

    let generate_ail_stat (id, it) = 
      let (b, s, e) = cn_to_ail_expr_aux_internal const_prop pred_name dts it PassBack in
      (* Res ident later gets replaced by correct variable if being called from DatatypeCons *)
      let ail_memberof = A.(AilEmemberofptr (mk_expr res_ident, id)) in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (mk_expr ail_memberof, e)))) in
      (b, s, assign_stat)
    in

    let (b, s) = match pred_name with 
      (* Assuming records only get instantiated at point of return for predicates *)
      | Some sym -> 
          let sym_name = generate_sym_with_suffix ~suffix:"_record" sym in
          let ctype_ = C.(Pointer (empty_qualifiers, (mk_ctype (Struct sym_name)))) in
          let res_binding = create_binding res_sym ctype_ in
          let fn_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (AilEsizeof (empty_qualifiers, mk_ctype C.(Struct sym_name)))])) in
          let alloc_stat = A.(AilSdeclaration [(res_sym, Some (mk_expr fn_call))]) in
          ([res_binding], [alloc_stat])
      (* Allocation taken care of if in datatype instantiation case - not needed here *)
      | None -> ([], [])
    in
    
    let (bs, ss, assign_stats) = list_split_three (List.map generate_ail_stat ms) in
    dest d (List.concat bs @ b, List.concat ss @ s @ assign_stats, mk_expr res_ident)

  | RecordUpdate ((t1, m), t2) -> failwith "TODO6"
  | DatatypeCons (sym, t) -> 
    (* sym is the constructor name, t is a record with members and values *)
    (* e.g. Tree_Node {k: 3, v: 0, l: Tree_Empty {}, r: Tree_Empty {}}*)

    (* Hacky way of finding datatype this comes from while pipeline being sorted out *)
    let rec find_dt_from_constructor constr_sym dts = 
      match dts with 
        | [] -> failwith "Datatype not found" (* Not found *)
        | dt :: dts' ->
          let matching_cases = List.filter (fun (c_sym, members) -> String.equal (Sym.pp_string c_sym) (Sym.pp_string constr_sym)) dt.cn_dt_cases in
          if List.length matching_cases != 0 then
            let (_, members) = List.hd matching_cases in
            (dt, members)
          else 
            find_dt_from_constructor constr_sym dts'
    in

    let (parent_dt, members) = find_dt_from_constructor sym dts in
    Printf.printf "Datatype name: %s\n" (Sym.pp_string parent_dt.cn_dt_name);
    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in
    let ctype_ = C.(Pointer (empty_qualifiers, (mk_ctype (Struct parent_dt.cn_dt_name)))) in
    let res_binding = create_binding res_sym ctype_ in
    let fn_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (AilEsizeof (empty_qualifiers, mk_ctype C.(Struct parent_dt.cn_dt_name)))])) in
    let ail_decl = A.(AilSdeclaration [(res_sym, Some (mk_expr fn_call))]) in
    Printf.printf "Reached past allocation declaration\n";
    (* Ignore e in this case *)
    let (b, ss, e) = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in

    (* Another hack *)
    let lc_constr_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true sym in 

    let rec modify_ail_stats = function
      | [] -> []
      | (A.(AilSexpr (A.(AnnotatedExpression (_, _, _, AilEassign (lhs, rhs)))))) :: ss -> 
        let new_lhs = (match rm_expr lhs with 
          | A.(AilEmemberofptr (_, id)) ->
            (* TODO: Make check for which exprs to modify more precise *)
            if (Id.equal id (Id.id "tag")) then lhs else 
            let e_ = A.(AilEmemberofptr (mk_expr res_ident, Id.id "u")) in
            let e_' = A.(AilEmemberof (mk_expr e_, create_id_from_sym lc_constr_sym)) in
            let e_'' = A.(AilEmemberof (mk_expr e_', id)) in
            mk_expr e_''
          | _ -> lhs)
        in
        let new_stat_ = A.(AilSexpr (mk_expr (AilEassign (new_lhs, rhs)))) in
        new_stat_ :: modify_ail_stats ss
      | s :: ss -> s :: modify_ail_stats ss
    in 


    let modified_stats = modify_ail_stats ss in

    let uc_constr_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true sym in
    let tag_member_ptr = A.(AilEmemberofptr (mk_expr res_ident, Id.id "tag")) in
    let tag_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr tag_member_ptr, mk_expr (AilEident uc_constr_sym))))) in

    dest d (b @ [res_binding], [ail_decl; tag_assign] @ modified_stats, mk_expr res_ident)

  | DatatypeMember (it, id) -> 
    (* Case of single constructor in datatype *)
    let (b, s, e) = cn_to_ail_expr_aux_internal const_prop pred_name dts it PassBack in
    let ail_expr_ = A.(AilEmemberofptr (e, Id.id "u")) in
    let constructor_sym = match IT.bt it with
      | Datatype sym -> 
        let dt = List.hd (List.filter (fun d -> String.equal (Sym.pp_string sym) (Sym.pp_string d.cn_dt_name)) dts) in
        let constructors = List.map fst dt.cn_dt_cases in
        generate_sym_with_suffix ~suffix:"" ~lowercase:true (List.hd constructors)
      | _ -> failwith "Can only get datatype member from term of type datatype"
    in
    let ail_expr_' = A.(AilEmemberof (mk_expr ail_expr_, create_id_from_sym constructor_sym)) in
    dest d (b, s, mk_expr A.(AilEmemberof (mk_expr ail_expr_', id)))

  | DatatypeIsCons (sym, it) -> 
    cn_to_ail_expr_aux_internal const_prop pred_name dts it d

  (* Allocation *)
  | Constructor (nm, ms) -> 
    let (ids, ts) = List.split ms in
    let bs_ss_es = List.map (fun t -> cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack) ts in
    let (bs, ss, es) = list_split_three bs_ss_es in
    let ms' = List.combine ids (List.map (fun e -> Some e) es) in
    dest d (List.concat bs, List.concat ss, mk_expr (AilEstruct (nm, ms')))

  | MemberShift (_, tag, member) -> 
    let ail_expr_ = A.(AilEoffsetof (C.(Ctype ([], Struct tag)), member)) in
    dest d ([], [], mk_expr ail_expr_)

  | ArrayShift _ -> failwith "TODO7"
  | Nil bt -> failwith "TODO8"
  | Cons (x, xs) -> failwith "TODO9"
  | Head xs -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts xs PassBack in
    (* dereference to get first value, where xs is assumed to be a pointer *)
    let ail_expr_ = A.(AilEunary (Indirection, e)) in 
    dest d (b, s, mk_expr ail_expr_)

  | Tail xs -> failwith "TODO11"
  | NthList (t1, t2, t3) -> failwith "TODO12"
  | ArrayToList (t1, t2, t3) -> failwith "TODO13"
  | Representable (ct, t) -> failwith "TODO14"
  | Good (ct, t) -> 
    cn_to_ail_expr_aux_internal const_prop pred_name dts t d
    
  | Aligned t_and_align -> failwith "TODO16"
  | WrapI (ct, t) -> 
    cn_to_ail_expr_aux_internal const_prop pred_name dts t d

  | MapConst (bt, t) -> failwith "TODO18"
  | MapSet (t1, t2, t3) -> failwith "TODO19"
  | MapGet (arr, index) ->
    (* Only works when index is an integer *)
    (* TODO: Make it work for general case *)
    (* TODO: Do general allocation stuff *)
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts arr PassBack in
    let (b2, s2, e2) = cn_to_ail_expr_aux_internal const_prop pred_name dts index PassBack in
    let ail_sub_expr_ = mk_expr (A.(AilEbinary (e1, Arithmetic Add, e2))) in
    dest d (b1 @ b2, s1 @ s2, mk_expr A.(AilEunary (Indirection, ail_sub_expr_)))

  | MapDef ((sym, bt), t) -> failwith "TODO21"
  | Apply (sym, ts) ->
      let bs_ss_es = List.map (fun e -> cn_to_ail_expr_aux_internal const_prop pred_name dts e PassBack) ts in
      let (bs, ss, es) = list_split_three bs_ss_es in 
      let f = (mk_expr A.(AilEident sym)) in
      let ail_expr_ = A.AilEcall (f, es) in 
      dest d (List.concat bs, List.concat ss, mk_expr ail_expr_)
      
  | Let ((var, t1), body) -> 
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts t1 PassBack in
    let ctype_ = cn_to_ail_base_type (bt_to_cn_base_type (IT.bt t1)) in
    let binding = create_binding var ctype_ in
    let ail_assign = A.(AilSdeclaration [(var, Some e1)]) in
    prefix d (b1 @ [binding], s1 @ [ail_assign]) (cn_to_ail_expr_aux_internal const_prop pred_name dts body d)

  | Match (t, ps) -> 
      Printf.printf "Reached pattern matching case\n";

      (* PATTERN COMPILER *)

      let mk_pattern pattern_ bt = T.(Pat (pattern_, bt)) in

      let simplify_leading_variable t1 (ps, t2) =
        match ps with 
        | T.(Pat (PSym sym', p_bt)) :: ps' -> ((mk_pattern T.PWild p_bt):: ps', T.(IT (Let ((sym', t1), t2), IT.basetype t2)))
        | p :: ps' -> (p :: ps', t2)
        | [] -> assert false
      in

      let leading_wildcard (ps, _) =
        match ps with
          | T.(Pat (PWild, _)) :: ps' -> true
          | _ :: ps' -> false
          | [] -> failwith "Empty patterns not allowed"
      in

      let expand_datatype c (ps, e) = 
        match ps with 
        | T.(Pat (PWild, p_bt) as pat) :: ps' -> Some (pat :: ps', e)
        | T.(Pat (PConstructor (c_nm, members), _)) :: ps' ->
          if Sym.equal_sym c c_nm then
            let member_patterns = List.map snd members in
            Some (member_patterns @ ps', e)
          else
            None
        | _ :: _ -> failwith "Non-sum pattern" 
        | [] -> assert false 
      in 

      let transform_switch_expr e
        = A.(AilEmemberofptr (e, Id.id "tag"))
      in

      (* TODO: Incorporate destination passing recursively into this. Might need PassBack throughout, like in cn_to_ail_expr_aux function *)
      (* Matrix algorithm for pattern compilation *)
      let rec translate : int -> (BT.basetype Terms.term) list -> (BT.basetype Terms.pattern list * BT.basetype Terms.term) list -> (A.bindings * (_ A.statement_) list) =
        fun count vars cases -> 
          match vars with 
            | [] ->
              (match cases with 
              | ([], t) :: rest -> 
                let (bs, ss) = 
                  (match d with 
                    | Assert -> 
                      cn_to_ail_expr_aux_internal const_prop pred_name dts t Assert
                    | Return -> 
                      cn_to_ail_expr_aux_internal const_prop pred_name dts t Return
                    | AssignVar x -> 
                      cn_to_ail_expr_aux_internal const_prop pred_name dts t (AssignVar x)
                    | PassBack -> 
                      failwith "TODO Pattern Match PassBack")
                in 
                (bs, ss)
              | [] -> failwith "Incomplete pattern match"
              | ((_::_), e) :: rest -> assert false)

            | term :: vs -> 
              
              let cases = List.map (simplify_leading_variable term) cases in

              if List.for_all leading_wildcard cases then
                let cases = List.map (fun (ps, e) -> (List.tl ps, e)) cases in
                let (bindings', stats') = translate count vs cases in 
                (bindings', stats')
              else
                match IT.bt term with
                  | BT.Datatype sym -> 
                      Printf.printf "Inside datatype case. Sym = %s\n" (Sym.pp_string sym);

                      let cn_dt = List.filter (fun dt -> String.equal (Sym.pp_string sym) (Sym.pp_string dt.cn_dt_name)) dts in 
                      (match cn_dt with 
                        | [] -> failwith "Datatype not found"
                        | dt :: _ ->
                          let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts term PassBack in
                          let build_case (constr_sym, members_with_types) = 
                            let (ts, ids) = List.split members_with_types in
                            let bts = List.map cn_base_type_to_bt ts in
                            let vars' = List.map (fun id -> T.StructMember (term, id)) ids in
                            let terms' = List.map (fun (var', bt') -> T.IT (var', bt')) (List.combine vars' bts) in
                            let cases' = List.filter_map (expand_datatype constr_sym) cases in 
                            let suffix = "_" ^ (string_of_int count) in
                            let lc_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true constr_sym in 
                            let count_sym = generate_sym_with_suffix ~suffix ~lowercase:true constr_sym in 
                            let rhs_memberof_ptr = A.(AilEmemberofptr (e1, Id.id "u")) in (* TODO: Remove hack *)
                            let rhs_memberof = A.(AilEmemberof (mk_expr rhs_memberof_ptr, create_id_from_sym lc_sym)) in
                            let constructor_var_assign = mk_stmt A.(AilSdeclaration [(count_sym, Some (mk_expr rhs_memberof))]) in

                            let (bindings, member_stats) = translate (count + 1) (terms' @ vs) cases' in
                            (* TODO: Check *)
                            let stat_block = A.AilSblock (bindings, constructor_var_assign :: (List.map mk_stmt member_stats)) in
                            let tag_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true constr_sym in
                            let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, Sym.pp_string tag_sym); attr_args = []} in
                            let ail_case = A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt stat_block)) in
                            let ail_case_stmt = A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case)) in
                            ail_case_stmt
                          in 
                          let e1_transformed = transform_switch_expr e1 in
                          let ail_case_stmts = List.map build_case dt.cn_dt_cases in
                          let switch = A.(AilSswitch (mk_expr e1_transformed, mk_stmt (AilSblock ([], ail_case_stmts)))) in
                          (b1, s1 @ [switch])
                      )
                  | _ -> 
                    (* Cannot have non-variable, non-wildcard pattern besides struct *)
                    failwith "Unexpected pattern"
      in

      let translate_real : type a. (BT.basetype Terms.term) list -> (BT.basetype Terms.pattern list * BT.basetype Terms.term) list -> a dest -> a =
        fun vars cases d ->
          let (bs, ss) = translate 1 vars cases in
          match d with 
            | Assert -> (bs, ss)
            | Return -> (bs, ss)
            | AssignVar x -> failwith "TODO translate_real 1"
            | PassBack -> failwith "TODO translate_real 2"
      in 

      let ps' = List.map (fun (p, t) -> ([p], t)) ps in
      translate_real [t] ps' d

  | Cast (bt, t) -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts t PassBack in
    let ail_expr_ = A.(AilEcast (empty_qualifiers, C.Ctype ([], cn_to_ail_base_type (bt_to_cn_base_type bt)), e)) in 
    dest d (b, s, mk_expr ail_expr_)

  (* | _ -> failwith "TODO: default case" *)

let cn_to_ail_expr_internal
  : type a. (_ Cn.cn_datatype) list -> IT.t -> a dest -> a
  = fun dts cn_expr d ->
    cn_to_ail_expr_aux_internal None None dts cn_expr d

let cn_to_ail_expr_internal_with_pred_name
  : type a. Sym.sym -> (_ Cn.cn_datatype) list -> IT.t -> a dest -> a
    = fun pred_name dts cn_expr d ->
      cn_to_ail_expr_aux_internal None (Some pred_name) dts cn_expr d    


let create_member (ctype_, id) =
  (id, (empty_attributes, None, empty_qualifiers, mk_ctype ctype_))


let generate_tag_definition dt_members = 
  let ail_dt_members = List.map (fun (cn_type, id) -> (cn_to_ail_base_type cn_type, id)) dt_members in
  (* TODO: Check if something called tag already exists *)
  let members = List.map create_member ail_dt_members in
  C.(StructDef (members, None))

let generate_struct_definition ?(lc=true) (constructor, members) = 
  let constr_sym = if lc then
    Sym.fresh_pretty (String.lowercase_ascii (Sym.pp_string constructor))
  else
  constructor 
  in
  (constr_sym, (empty_attributes, generate_tag_definition members))


let cn_to_ail_pred_records = 
  let map_bindings = RecordMap.bindings !records in
  let flipped_bindings = List.map (fun (ms, sym) -> (sym, ms)) map_bindings in
  List.map generate_struct_definition flipped_bindings



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
  let enum = (enum_sym, (attrs, enum_tag_definition)) in
  let cntype_sym = Sym.fresh_pretty "cntype" in

  let cntype_pointer = C.(Pointer (empty_qualifiers, mk_ctype (Struct cntype_sym))) in
  let extra_members tag_type = [
      (create_member (tag_type, Id.id "tag"));
      (create_member (cntype_pointer, Id.id "cntype"))]
  in
  
  let structs = List.map (fun c -> generate_struct_definition c) cn_datatype.cn_dt_cases in
  let structs = if first then 
    let generic_dt_struct = 
      (generic_cn_dt_sym, (empty_attributes, C.(StructDef (extra_members (C.(Basic (Integer (Signed Int_)))), None))))
    in
    let cntype_struct = (cntype_sym, (empty_attributes, C.(StructDef ([], None)))) in
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

  let structs = structs @ [(union_sym, (empty_attributes, union_def)); (cn_datatype.cn_dt_name, (empty_attributes, C.(StructDef ((extra_members (C.(Basic (Integer (Enum enum_sym))))) @ [union_member], None))))] in
  enum :: structs

let cn_to_ail_resource_internal sym dts (preds : Mucore.T.resource_predicates) =
  (* Binding will be different depending on whether it's a p or q - q is array*)
  let make_deref_expr_ e_ = A.(AilEunary (Indirection, mk_expr e_)) in 
  function
  | ResourceTypes.P p -> 
    let _pt_ctype_ =  bt_to_ail_ctype (IT.bt p.pointer) in
    (* TODO: Come back to this to mirror q case *)
    (* TODO: Extract code that is common between p and q cases to avoid duplication *)
    let ctype_ = match p.name with 
      | Owned (sct, _) -> rm_ctype (Sctypes.to_ctype sct)
      | PName pred_name -> 
        let pred_record_name = generate_sym_with_suffix ~suffix:"_record" pred_name in
        C.(Pointer (empty_qualifiers, (mk_ctype (Struct pred_record_name))))
    in
    Printf.printf "Resource var name: %s\n" (Sym.pp_string sym);

    let binding = create_binding sym ctype_ in

    let (b, s, e) = cn_to_ail_expr_internal dts p.pointer PassBack in
    let (rhs, bs, ss) = match p.name with 
      | Owned _ ->
        let cast_ctype_pointer = C.(Pointer (empty_qualifiers, mk_ctype ctype_)) in
        let cast_e_ = A.(AilEcast (empty_qualifiers, mk_ctype cast_ctype_pointer, e)) in
        (make_deref_expr_ cast_e_, [], [])
      | PName pname -> 
        let (bs, ss, es) = list_split_three (List.map (fun it -> cn_to_ail_expr_internal dts it PassBack) p.iargs) in
        let fcall = A.(AilEcall (mk_expr (AilEident pname), e :: es)) in
        (fcall, bs, ss)
    in
    let s_decl = A.(AilSdeclaration [(sym, Some (mk_expr rhs))]) in
    (b @ (List.concat bs) @ [binding], s @ (List.concat ss) @ [s_decl])

  | ResourceTypes.Q q -> 
    (* 
      Input is expr of the form:
      take sym = each (integer q.q; q.permission){ Owned(q.pointer + (q.q * q.step)) }
    *)
    let (b1, s1, e1) = cn_to_ail_expr_internal dts q.pointer PassBack in
    let (b2, s2, e2) = cn_to_ail_expr_internal dts q.permission PassBack in
    let (b3, s3, e3) = cn_to_ail_expr_internal dts q.step PassBack in


    (*
      Generating a loop of the form:
      <set q.q to start value>
      while (q.permission.snd) {
        *(sym + q.q * q.step) = *(q.pointer + q.q * q.step);
        q.q++;
      } 
    *)

    let i_sym = q.q in

    let start_expr = generate_start_expr (get_leftmost_and_expr (rm_expr e2)) q.q in
    let end_cond = get_rest_of_expr_r (rm_expr e2) in


    let start_binding = create_binding i_sym C.(Basic (Integer (Signed Int_))) in
    let start_assign = A.(AilSdeclaration [(i_sym, Some start_expr)]) in

    let q_times_step = A.(AilEbinary (mk_expr (AilEident i_sym), Arithmetic Mul, e3)) in
    let gen_add_expr_ e_ = 
      A.(AilEbinary (mk_expr e_, Arithmetic Add, mk_expr q_times_step))
    in
    let sym_add_expr = make_deref_expr_ (gen_add_expr_ A.(AilEident sym)) in

    (* let ctype_ =  bt_to_ail_ctype (IT.bt q.pointer) in *)
    let ctype_ = match q.name with 
      | Owned (sct, _) -> rm_ctype (Sctypes.to_ctype sct)
      | PName pname -> 
        let matching_preds = List.filter (fun (pred_sym', def) -> String.equal (Sym.pp_string pname) (Sym.pp_string pred_sym')) preds in
        let (pred_sym', pred_def') = match matching_preds with 
          | [] -> failwith "Predicate not found"
          | p :: _ -> p
        in 
        let cn_bt = bt_to_cn_base_type pred_def'.oarg_bt in
        match cn_bt with 
          | CN_record _ ->
            let pred_record_name = generate_sym_with_suffix ~suffix:"_record" pred_sym' in
            C.(Pointer (empty_qualifiers, (mk_ctype (Struct pred_record_name))))
          | _ -> cn_to_ail_base_type ~pred_sym:(Some pred_sym') cn_bt
    in

    let (rhs, bs, ss) = match q.name with 
      | Owned _ -> (make_deref_expr_ (gen_add_expr_ (rm_expr e1)), [], [])
      | PName pname -> 
        let (bs, ss, es) = list_split_three (List.map (fun it -> cn_to_ail_expr_internal dts it PassBack) q.iargs) in
        let fcall = A.(AilEcall (mk_expr (AilEident pname), (mk_expr (gen_add_expr_ (rm_expr e1))) :: es)) in
        (fcall, bs, ss)
    in

    (* let pointer_type = match ctype_ with 
      | C.(Pointer (_, Ctype (_, Void))) -> ctype_
      | ct_ -> C.(Pointer (empty_qualifiers, mk_ctype ct_))
    in *)
    let increment_stat = A.(AilSexpr (mk_expr (AilEunary (PostfixIncr, mk_expr (AilEident i_sym))))) in 

    let (bs', ss') = match ctype_ with 
      | C.Void -> 
        let void_pred_call = A.(AilSexpr (mk_expr rhs)) in
        let while_loop = A.(AilSwhile (mk_expr end_cond, mk_stmt (AilSblock ([], List.map mk_stmt [void_pred_call; increment_stat])), 0)) in
        let ail_block = A.(AilSblock ([], List.map mk_stmt [start_assign; while_loop])) in
        ([], [ail_block])
      | _ -> 
        let sym_binding = create_binding sym C.(Pointer (empty_qualifiers, mk_ctype ctype_)) in
        let alloc_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (A.(AilEconst (ConstantInteger (IConstant (Z.of_int 10000, Decimal, None)))))])) in
        let sym_decl = A.(AilSdeclaration [(sym, Some (mk_expr alloc_call))]) in
        let ail_assign_stat = A.(AilSexpr (mk_expr (AilEassign (mk_expr sym_add_expr, mk_expr rhs)))) in
        let while_loop = A.(AilSwhile (mk_expr end_cond, mk_stmt (AilSblock ([], List.map mk_stmt [ail_assign_stat; increment_stat])), 0)) in
        let ail_block = A.(AilSblock ([], List.map mk_stmt [start_assign; while_loop])) in
        ([sym_binding], [sym_decl; ail_block])
    in

    (b1 @ b2 @ b3 @ [start_binding] @ bs' @ (List.concat bs), s1 @ s2 @ s3 @ (List.concat ss) @ ss')

let cn_to_ail_logical_constraint_internal : type a. (_ Cn.cn_datatype) list -> a dest -> LC.logical_constraint -> a
  = fun dts d lc -> 
      match lc with
      | LogicalConstraints.T it -> 
        Printf.printf "Reached logical constraint function\n";
        cn_to_ail_expr_internal dts it d
      | LogicalConstraints.Forall ((sym, bt), it) -> 
        Printf.printf "Reached logical constraint function FORALL\n";
        let (cond_it, t) = match IT.term it with 
          | Binop (Impl, it, it') -> (it, it')
          | _ -> failwith "Incorrect form of forall logical constraint term"
        in

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

        let (b1, s1, e1) = cn_to_ail_expr_internal dts cond_it PassBack in
        let t_translated = cn_to_ail_expr_internal dts t PassBack in

        let start_expr = generate_start_expr (get_leftmost_and_expr (rm_expr e1)) sym in
        let while_cond = get_rest_of_expr_r (rm_expr e1) in

        let (bs, ss, e) = gen_bool_while_loop sym (rm_expr start_expr) while_cond t_translated in 
        dest d (bs, ss, e)
        (* Pp.c_app !^"forall" [Sym.pp s; BT.pp bt] ^^ dot ^^^ IT.pp it *)
    
  


(* TODO: Finish with rest of function - maybe header file with A.Decl_function (cn.h?) *)
let cn_to_ail_function_internal (fn_sym, (def : LogicalFunctions.definition)) cn_datatypes = 
  let (bs, ail_func_body) =
  match def.definition with
    | Def it ->
      let (bs, ss) = cn_to_ail_expr_internal cn_datatypes it Return in
      (bs, List.map mk_stmt ss)
    | _ -> ([], []) (* TODO: Other cases *)
  in
  let ret_type = cn_to_ail_base_type (bt_to_cn_base_type def.return_bt) in
  let params = List.map (fun (sym, bt) -> (sym, mk_ctype (cn_to_ail_base_type (bt_to_cn_base_type bt)))) def.args in
  let (param_syms, param_types) = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  (* Generating function declaration *)
  let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, mk_ctype ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = (fn_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (bs, ail_func_body)))) in
  (decl, def)

let cn_to_ail_predicate_internal (pred_sym, (def : ResourcePredicates.definition)) dts preds = 
  let rec predicate_clause_to_ail = function
      | LAT.Define ((name, it), info, lat) -> 
        let ctype_ = bt_to_ail_ctype (IT.bt it) in
        let binding = create_binding name ctype_ in
        let (b1, s1) = cn_to_ail_expr_internal_with_pred_name pred_sym dts it (AssignVar name) in
        let (b2, s2) = predicate_clause_to_ail lat in
        (b1 @ b2 @ [binding], s1 @ s2)

      | LAT.Resource ((name, (ret, bt)), info, lat) -> 
        let (b1, s1) = cn_to_ail_resource_internal name dts preds ret in
        let (b2, s2) = predicate_clause_to_ail lat in
        (b1 @ b2, s1 @ s2)

      | LAT.Constraint (lc, (loc, str_opt), lat) -> 
        let (b1, s, e) = cn_to_ail_logical_constraint_internal dts PassBack lc in
        (* TODO: Check this logic *)
        let ss = match str_opt with 
          | Some info -> 
            (* Printf.printf "Logical constraint info: %s\n" info; *)
            []
          | None -> 
            (* Printf.printf "No logical constraint info\n"; *)
            let ail_stat_ = A.(AilSexpr (mk_expr (AilEassert e))) in
            s @ [ail_stat_]
        in
        let (b2, s2) = predicate_clause_to_ail lat in
        (b1 @ b2, ss @ s2)

      | LAT.I it ->
        cn_to_ail_expr_internal_with_pred_name pred_sym dts it Return
  in

  let rec clause_translate (clauses : RP.clause list) = 
    match clauses with
      | [] -> ([], [])
      | c :: cs ->
        let (bs, ss) = predicate_clause_to_ail c.packing_ft in
        match c.guard with 
          | IT (Const (Bool true), _) -> 
            let (bs'', ss'') = clause_translate cs in
            (bs @ bs'', ss @ ss'')
          | _ -> 
            let (b1, s1, e) = cn_to_ail_expr_internal_with_pred_name pred_sym dts c.guard PassBack in
            let (bs'', ss'') = clause_translate cs in
            let ail_if_stat = A.(AilSif (e, mk_stmt (AilSblock (bs, List.map mk_stmt ss)), mk_stmt (AilSblock (bs'', List.map mk_stmt ss'')))) in
            ([], [ail_if_stat])
  in

  let (bs, ss) = match def.clauses with 
    | Some clauses -> clause_translate clauses
    | None -> ([], [])
  in

  let pred_body = List.map mk_stmt ss in

  let ail_record_opt = match def.oarg_bt with
    | BT.Record members ->
      let flipped_members = List.map (fun (id, bt) -> (bt_to_cn_base_type bt, id)) members in
      let record_sym = generate_sym_with_suffix ~suffix:"_record" pred_sym in
      Some (generate_struct_definition ~lc:false (record_sym, flipped_members))
    | _ -> None
  in

  let ret_type = cn_to_ail_base_type ~pred_sym:(Some pred_sym) (bt_to_cn_base_type def.oarg_bt) in
  let params = List.map (fun (sym, bt) -> (sym, mk_ctype  (bt_to_ail_ctype bt))) ((def.pointer, BT.Loc) :: def.iargs) in
  let (param_syms, param_types) = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  (* Generating function declaration *)
  let decl = (pred_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, mk_ctype ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = (pred_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (bs, pred_body)))) in
  ((decl, def), ail_record_opt)




let rec cn_to_ail_arguments_l_internal dts preds = function
    (* CN let *)
  | M_Define ((sym, it), _info, l) ->
    let binding = create_binding sym (bt_to_ail_ctype (IT.bt it)) in
    let (b1, s1) = cn_to_ail_expr_internal dts it (AssignVar sym) in
    let (b2, s2) = cn_to_ail_arguments_l_internal dts preds l in
    (b1 @ b2 @ [binding], s1 @ s2)

    (* CN take *)
  | M_Resource ((sym, (re, _bt)), _info, l) -> 
    (* Printf.printf "Reached M_Resource (Owned)\n"; *)
    let (b1, s1) = cn_to_ail_resource_internal sym dts preds re in
    let (b2, s2) = cn_to_ail_arguments_l_internal dts preds l in
    (b1 @ b2, s1 @ s2)

    (* CN assertion (or inside of take) *)
  | M_Constraint (lc, _info, l) -> 
    (* Printf.printf "Reached M_Constraint (take)\n"; *)
    (* let (s, e) = cn_to_ail_logical_constraint_internal dts lc in
    let ail_stat_ = A.(AilSexpr (mk_expr e)) in
    s @ ail_stat_ ::  *)
    (* TODO: Check for assertion case *)
    cn_to_ail_arguments_l_internal dts preds l
     (* Pp.parens (LogicalConstraints.pp lc) ^^^ pp_mu_arguments_l ppf l *)
  | M_I i -> ([], [])
  (* failwith "TODO" *)
     (* !^"->" ^^^ Pp.parens (ppf i) *)

let rec cn_to_ail_arguments_internal dts preds = function
  | M_Computational ((s, bt), _info, a) ->
    (* TODO: Do something with s and bt *)
      cn_to_ail_arguments_internal dts preds a
  | M_L l ->
      cn_to_ail_arguments_l_internal dts preds l

(* TODO: Generate bindings *)
(* TODO: Add destination passing? *)
let rec cn_to_ail_post_aux_internal dts preds = function
  | LRT.Define ((name, it), info, t) ->
    Printf.printf "LRT.Define\n";
    let binding = create_binding name (bt_to_ail_ctype (IT.bt it)) in
    let (b1, s1) = cn_to_ail_expr_internal dts it (AssignVar name) in
    let (b2, s2) = cn_to_ail_post_aux_internal dts preds t in
    (b1 @ b2 @ [binding], s1 @ s2)

  | LRT.Resource ((name, (re, bt)), info, t)  ->
    Printf.printf "LRT.Resource\n";
    let (b1, s1) = cn_to_ail_resource_internal name dts preds re in
    let (b2, s2) = cn_to_ail_post_aux_internal dts preds t in
    (b1 @ b2, s1 @ s2)

  | LRT.Constraint (lc, (loc, str_opt), t) -> 
    Printf.printf "LRT.Constraint\n";
    let (b1, s, e) = cn_to_ail_logical_constraint_internal dts PassBack lc in
    (* TODO: Check this logic *)
    let ss = match str_opt with 
      | Some info -> 
        Printf.printf "Logical constraint info: %s\n" info;
        []
      | None -> 
        Printf.printf "No logical constraint info\n";
        let ail_stat_ = A.(AilSexpr (mk_expr (AilEassert e))) in
        s @ [ail_stat_]
    in
    let (b2, s2) = cn_to_ail_post_aux_internal dts preds t in

    (b1 @ b2, ss @ s2)

  | LRT.I -> ([], [])


let cn_to_ail_post_internal dts preds (ReturnTypes.Computational (bound, oinfo, t)) = 
  cn_to_ail_post_aux_internal dts preds t

(* TODO: Add destination passing *)
let cn_to_ail_cnstatement_internal : type a. (_ Cn.cn_datatype) list -> a dest -> Cnprog.cn_statement -> (a * bool)
= fun dts d cnstatement ->
  let default_true_res = cn_to_ail_expr_internal dts (IT (Const (Bool true), BT.Bool)) d in
  match cnstatement with
  | Cnprog.M_CN_pack_unpack (pack_unpack, pt) -> 
    (default_true_res, true)

  | Cnprog.M_CN_have lc -> failwith "TODO M_CN_have"

  | Cnprog.M_CN_instantiate (o_s, it) -> 
    (default_true_res, true)

  | Cnprog.M_CN_extract (to_extract, it) -> 
    (default_true_res, true)

  | Cnprog.M_CN_unfold (fsym, args) -> 
    (default_true_res, true)
    (* fsym is a function symbol *)

  | Cnprog.M_CN_apply (fsym, args) -> 
    (* Can ignore *)
    (* TODO: Make type correct from return type of top-level CN functions - although it shouldn't really matter (?) *)
    (default_true_res, true)
    (* fsym is a lemma symbol *)

  | Cnprog.M_CN_assert lc -> 
    (cn_to_ail_logical_constraint_internal dts d lc, false)

  | Cnprog.M_CN_inline _ -> failwith "TODO M_CN_inline"


let rec cn_to_ail_cnprog_internal_aux dts = function
| Cnprog.M_CN_let (loc, (name, {ct; pointer}), prog) -> 
  Printf.printf "In M_CN_let\n";
  let (b1, s, e) = cn_to_ail_expr_internal dts pointer PassBack in
  let ail_deref_expr_ = A.(AilEunary (Indirection, e)) in
  (* TODO: Use ct for type binding *)
  (* TODO: Differentiate between read and deref cases for M_CN_let *)
  let standardise_sym sym' = 
    let sym_str = Sym.pp_string sym' in
    let new_sym_str = String.map (fun c -> 
      if Char.equal c '&' then '_' else c) sym_str in
    Sym.fresh_pretty new_sym_str
    in 
  let name = standardise_sym name in

  let ct_ = rm_ctype (Sctypes.to_ctype ct) in
  let ct_without_ptr = match ct_ with 
    | C.(Pointer (_, ct)) -> rm_ctype ct
    | ct_' -> ct_'
  in
  let binding = create_binding name ct_without_ptr in
 
  let ail_stat_ = A.(AilSdeclaration [(name, Some (mk_expr ail_deref_expr_))]) in
  (* let ail_stat_ = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident name), mk_expr ail_deref_expr_)))) in *)
  let ((loc', b2, ss), no_op) = cn_to_ail_cnprog_internal_aux dts prog in
  if no_op then
    ((loc', [], []), true)
  else
    ((loc', b1 @ b2 @ [binding], s @ ail_stat_ :: ss), true)

| Cnprog.M_CN_statement (loc, stmt) ->
  (* (loc, [], [empty_ail_stmt]) *)
  Printf.printf "In M_CN_statement\n";
  let ((bs, ss), no_op) = cn_to_ail_cnstatement_internal dts Assert stmt in 
  ((loc, bs, ss), no_op)

let cn_to_ail_cnprog_internal dts cn_prog =
  let ((loc, bs, ss), _) = cn_to_ail_cnprog_internal_aux dts cn_prog in
  (loc, bs, ss)