[@@@warning "-27"]
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
module AT=ArgumentTypes

let true_const = A.AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int true), Decimal, Some B)))

let map_basetypes = function 
  | BT.Map (bt1, bt2) -> (bt1, bt2)
  | _ -> failwith "Not a map"

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
    let ms' = List.map (fun (id, bt) -> (id, cn_base_type_to_bt bt)) ms in
    BT.Record ms'
  | CN_map (type1, type2) -> BT.Map (cn_base_type_to_bt type1, cn_base_type_to_bt type2)
  | CN_list typ -> cn_base_type_to_bt typ
  | CN_tuple ts -> BT.Tuple (List.map cn_base_type_to_bt ts)
  | CN_set typ -> cn_base_type_to_bt typ
  | CN_user_type_name _ -> failwith "TODO"
  | CN_c_typedef_name _ -> failwith "TODO"
  

module MembersKey = struct
  type t = (Id.t * symbol cn_base_type) list
  let rec compare (ms : t) ms' =
    match (ms, ms') with 
      | ([], []) -> 0
      | (_, []) -> 1
      | ([], _) -> -1
      | ((id, _) :: ms, (id', _) :: ms') -> 
        let c = String.compare (Id.s id) (Id.s id') in
        if c == 0 then
          0
        else
          compare ms ms'

    
end



let members_equal ms ms' = 
  if ((List.length ms) != (List.length ms')) then false else
  (if (List.length ms == 0) then true else (
  let (ids, cn_bts) = List.split ms in
  let (ids', cn_bts') = List.split ms' in
  let ctypes_eq = List.map2 (fun cn_bt cn_bt'->
    let bt = cn_base_type_to_bt cn_bt in
    let bt' = cn_base_type_to_bt cn_bt' in
    BT.equal bt bt') cn_bts cn_bts' in
  let ctypes_eq = List.fold_left (&&) true ctypes_eq in
  let ids_eq = List.map2 Id.equal ids ids' in
  let ids_eq = List.fold_left (&&) true ids_eq in
  ctypes_eq && ids_eq))

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

let create_binding sym ctype = 
  A.(sym, ((Cerb_location.unknown, Automatic, false), None, empty_qualifiers, ctype))

let cn_assert_sym = Sym.fresh_pretty "cn_assert"

let generate_cn_assert ail_expr = 
  A.(AilEcall (mk_expr (AilEident cn_assert_sym), [ail_expr]))
  

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
  let ms = List.map (fun (id, bt) -> (id, bt_to_cn_base_type bt)) member_types in
  CN_record ms
| BT.Map (bt1, bt2) -> CN_map (bt_to_cn_base_type bt1, bt_to_cn_base_type bt2)
| BT.List bt -> CN_list (bt_to_cn_base_type bt)
| BT.Tuple bts -> CN_tuple (List.map bt_to_cn_base_type bts)
| BT.Set bt -> CN_set (bt_to_cn_base_type bt)




(* TODO: Complete *)
let rec cn_to_ail_base_type ?(pred_sym=None) cn_typ = 
  let generate_ail_array bt = C.(Array (cn_to_ail_base_type bt, None)) in 
  let generate_record_sym sym members =  
    (match sym with
      | Some sym' -> 
        let sym'' = generate_sym_with_suffix ~suffix:"_record" sym' in
        records := RecordMap.add members sym'' !records;
        sym''
      | None ->   
        let map_bindings = RecordMap.bindings !records in
        let eq_members_bindings = List.filter (fun (k, v) -> members_equal k members) map_bindings in
        match eq_members_bindings with 
        | [] -> 
          (* First time reaching record of this type - add to map *)
          (let count = RecordMap.cardinal !records in
          let sym' = Sym.fresh_pretty ("record_" ^ (string_of_int count)) in
          records := RecordMap.add members sym' !records;
          sym')
        | (_, sym') :: _ -> 
          sym')
  in
  let typ = (match cn_typ with
  | CN_unit -> C.Void
  | CN_bool -> C.(Basic (Integer Bool))
  | CN_integer -> C.(Basic (Integer (Signed Long))) 
  (* TODO: Discuss integers *)
  | CN_bits _ -> failwith "TODO CN_bits"
  | CN_real -> failwith "TODO CN_real"
  | CN_loc -> C.(Pointer (empty_qualifiers, Ctype ([], Void))) (* Casting all CN pointers to void star *)
  | CN_alloc_id -> failwith "TODO CN_alloc_id"
  | CN_struct sym -> C.(Struct (generate_sym_with_suffix ~suffix:"_cn" sym))
  | CN_record members -> 
    let sym = generate_record_sym pred_sym members in
    Struct sym
   (* Every struct is converted into a struct pointer *)
   | CN_datatype sym -> Struct sym
   | CN_map (_, cn_bt) -> generate_ail_array cn_bt
   | CN_list bt -> generate_ail_array bt (* TODO: What is the optional second pair element for? Have just put None for now *)
   | CN_tuple ts -> 
      Printf.printf "Entered CN_tuple case\n";
      let some_id = create_id_from_sym (Sym.fresh_pretty "some_sym") in
      let members = List.map (fun t -> (some_id, t)) ts in
      let sym = generate_record_sym pred_sym members in
      Struct sym
   | CN_set bt -> generate_ail_array bt
   | CN_user_type_name _ -> failwith "TODO CN_user_type_name"
   | CN_c_typedef_name _ -> failwith "TODO CN_c_typedef_name")
  in 
  let annots = match cn_typ with 
    | CN_integer -> [CF.Annot.Atypedef (Sym.fresh_pretty "cn_integer")]
    | CN_bool -> [CF.Annot.Atypedef (Sym.fresh_pretty "cn_bool")]
    | CN_map _ -> [CF.Annot.Atypedef (Sym.fresh_pretty "cn_map")]
    | CN_loc -> [CF.Annot.Atypedef (Sym.fresh_pretty "cn_pointer")]
    | _ -> []
  in
  let ret = mk_ctype ~annots typ in
  match typ with 
    | C.Void -> ret 
    | _ -> mk_ctype C.(Pointer (empty_qualifiers, ret))

 

let bt_to_ail_ctype ?(pred_sym=None) t = cn_to_ail_base_type ~pred_sym (bt_to_cn_base_type t)

(* TODO: Finish *)
let cn_to_ail_unop_internal = function 
  | Terms.Not -> (A.Bnot, Some "cn_bool_not")
  (* | BWCLZNoSMT
  | BWCTZNoSMT
  | BWFFSNoSMT *)
  | _ -> failwith "TODO: unop translation"

(* TODO: Finish *)
let cn_to_ail_binop_internal bt1 bt2 = function
  | Terms.And -> (A.And, Some "cn_bool_and")
  | Or -> (A.Or, Some "cn_bool_or")
  (* | Impl *)
  | Add -> 
    (let str_opt = match bt1, bt2 with 
      | BT.Integer, BT.Integer -> Some "cn_integer_add"
      | BT.Loc, BT.Integer -> Some "cn_pointer_add"
      | _, _ -> None
    in
    (A.(Arithmetic Add), str_opt))
  | Sub -> 
    let str_opt = match bt1, bt2 with 
      | BT.Integer, BT.Integer -> Some "cn_integer_sub"
      | BT.Loc, BT.Integer -> Some "cn_pointer_sub"
      | _, _ -> None
    in
    (A.(Arithmetic Sub), str_opt)
  | Mul 
  | MulNoSMT -> (A.(Arithmetic Mul), Some "cn_integer_multiply")
  | Div 
  | DivNoSMT -> (A.(Arithmetic Div), Some "cn_integer_divide")
  | Exp
  | ExpNoSMT -> (A.And, Some "cn_integer_pow")
  (* | Rem
  | RemNoSMT *)
  | Mod
  | ModNoSMT -> (A.(Arithmetic Mod), Some "cn_integer_mod")
  | XORNoSMT -> (A.(Arithmetic Bxor), None)
  | BWAndNoSMT -> (A.(Arithmetic Band), None)
  | BWOrNoSMT -> (A.(Arithmetic Bor), None)
  | LT -> (A.Lt, Some "cn_integer_lt")
  | LE -> (A.Le, Some "cn_integer_le")
  | Min -> (A.And, Some "cn_integer_min")
  | Max -> (A.And, Some "cn_integer_max")
  | EQ -> (A.Eq, None) 
    (* let fn_str = match get_typedef_string (bt_to_ail_ctype bt1) with 
      | Some str -> Some (str ^ "_equality")
      | None -> None
    in
    (A.Eq, fn_str) *)
  | _ -> (A.And, None) (* TODO: Change *)
  (* | LTPointer
  | LEPointer
  | SetUnion
  | SetIntersection
  | SetDifference
  | SetMember
  | Subset *)

(* Assume a specific shape, where sym appears on the RHS (i.e. in e2) *)

let add_conversion_fn ail_expr_ bt = 
  let typedef_name = get_typedef_string (bt_to_ail_ctype bt) in 
  match typedef_name with 
  | Some str ->
    let str = String.concat "_" (String.split_on_char ' ' str) in
    A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty ("convert_to_" ^ str))), [mk_expr ail_expr_]))
  | None -> (match bt with 
      | BT.Struct sym -> 
        let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in 
        let conversion_fn_str = "convert_to_struct_" ^ (Sym.pp_string cn_sym) in 
        A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty conversion_fn_str)), [mk_expr ail_expr_]))
      | _ -> ail_expr_
    )
    

let rearrange_start_inequality sym e1 e2 = 
  match IT.term e2 with 
    | Terms.Binop (binop, (IT.IT (Sym sym1, _, _) as expr1), (IT.IT (Sym sym2, _, _) as expr2)) -> 
      (if String.equal (Sym.pp_string sym) (Sym.pp_string sym1) then
        let inverse_binop = match binop with 
          | Add -> Terms.Sub
          | Sub -> Add
          | _ -> failwith "Other binops not supported"
        in
        Terms.(Binop (inverse_binop, e1, expr2))
      else 
        (if String.equal (Sym.pp_string sym) (Sym.pp_string sym2) then 
          match binop with 
            | Add -> Terms.Binop (Sub, e1, expr1)
            | Sub -> failwith "Minus not supported"
            | _ -> failwith "Other binops not supported"
        else 
          failwith "Not of correct form"
        )
      )
    | _ -> failwith "TODO"



let generate_start_expr start_cond sym = 
  let (start_expr, binop) = 
    match IT.term start_cond with
      | Terms.(Binop (binop, expr1, IT.IT (Sym sym', _, _))) ->
          (if String.equal (Sym.pp_string sym) (Sym.pp_string sym') then
            (expr1, binop)
          else
            failwith "Not of correct form (unlikely case - i's not matching)")
      | Terms.(Binop (binop, expr1, expr2)) ->
          (IT.IT ((rearrange_start_inequality sym expr1 expr2), BT.Integer, Cerb_location.unknown), binop)
      | _ -> failwith "Not of correct form: more complicated RHS of binexpr than just i"
    in
    match binop with 
      | LE -> 
        start_expr
      | LT ->
        let one = IT.(IT (Const (Terms.Z (Z.of_int 1)), BT.Integer, Cerb_location.unknown)) in
        IT.(IT (Apply (Sym.fresh_pretty "cn_integer_add", [start_expr; one]), BT.Integer, Cerb_location.unknown)) 
      | _ -> failwith "Not of correct form: not Le or Lt"


let rec get_leftmost_and_expr = function
    | IT.IT (Terms.(Binop (And, lhs, rhs)), _, _) -> get_leftmost_and_expr lhs 
    | lhs -> lhs

let rec get_rest_of_expr_r it = match IT.term it with 
  | Terms.(Binop (And, lhs, rhs)) ->
    let r = get_rest_of_expr_r lhs in
    (match IT.term r with
      | Const (Bool true) -> rhs
      | _ -> IT.IT (Terms.(Binop (And, r, rhs)), BT.Bool, Cerb_location.unknown)
    )
  | lhs -> IT.IT (Const (Bool true), BT.Bool, Cerb_location.unknown)
  


let gen_bool_while_loop sym start_expr while_cond (bs, ss, e) = 
  (* 
     Input:
     each (integer sym; start_expr <= sym && while_cond) {t}

     where (bs, ss, e) = cn_internal_to_ail called on t with PassBack
  *)

  let b = Sym.fresh () in
  let b_ident = A.(AilEident b) in
  let b_binding = create_binding b (bt_to_ail_ctype BT.Bool) in
  let b_decl = A.(AilSdeclaration [(b, Some (mk_expr (add_conversion_fn true_const BT.Bool)))]) in

  let incr_var = A.(AilEident sym) in
  let incr_var_binding = create_binding sym (bt_to_ail_ctype BT.Integer) in
  let start_decl = A.(AilSdeclaration [(sym, Some (mk_expr start_expr))]) in

  let cn_bool_and_sym = Sym.fresh_pretty "cn_bool_and" in
  let rhs_and_expr_ = A.(AilEcall (mk_expr (AilEident cn_bool_and_sym), [mk_expr b_ident; e])) in
  let b_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr b_ident, mk_expr rhs_and_expr_)))) in
  (* let incr_stat = A.(AilSexpr (mk_expr (AilEunary (PostfixIncr, mk_expr incr_var)))) in *)
  let incr_stat = A.(AilSexpr (mk_expr (AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_integer_increment")), [mk_expr incr_var])))) in
  let convert_from_cn_bool_ident = mk_expr A.(AilEident (Sym.fresh_pretty "convert_from_cn_bool")) in
  let while_cond_with_conversion = mk_expr A.(AilEcall (convert_from_cn_bool_ident, [while_cond])) in
  let while_loop = A.(AilSwhile (while_cond_with_conversion, mk_stmt (AilSblock (bs, List.map mk_stmt (ss @ [b_assign; incr_stat]))), 0)) in

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

type ail_bindings_and_statements = A.bindings * CF.GenTypes.genTypeCategory A.statement_ list

type ail_executable_spec = {
    pre: ail_bindings_and_statements;
    post: ail_bindings_and_statements;
    in_stmt: (Locations.t * ail_bindings_and_statements) list;
    ownership_ctypes: CF.Ctype.ctype list;
}

let empty_ail_executable_spec = {
  pre = ([], []);
  post = ([], []);
  in_stmt = [];
  ownership_ctypes = [];
}

type 'a dest =
| Assert : ail_bindings_and_statements dest
| Return : ail_bindings_and_statements dest 
| AssignVar : C.union_tag -> ail_bindings_and_statements dest
| PassBack : (A.bindings * CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression) dest

let dest : type a. a dest -> A.bindings * CF.GenTypes.genTypeCategory A.statement_ list * CF.GenTypes.genTypeCategory A.expression -> a = 
  fun d (b, s, e) -> 
    match d with
    | Assert -> 
      let assert_stmt = A.(AilSexpr (mk_expr (generate_cn_assert e))) in
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




let generate_ownership_function ctype = 
  let ctype_str = str_of_ctype ctype in
  let ctype_str = String.concat "_" (String.split_on_char ' ' ctype_str) in
  let fn_sym = Sym.fresh_pretty ("owned_" ^ ctype_str) in
  let param1_sym = Sym.fresh_pretty "cn_ptr" in
  let param2_sym = Sym.fresh_pretty "owned_enum" in
  let param1 = (param1_sym, bt_to_ail_ctype BT.Loc) in
  let param2 = (param2_sym, mk_ctype (C.(Basic (Integer (Enum (Sym.fresh_pretty "OWNERSHIP")))))) in
  let (param_syms, param_types) = List.split [param1; param2] in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  let generate_case enum_str = 
    let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, enum_str); attr_args = []} in
    let ail_case = A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt AilSbreak)) in 
    A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case))
  in
  (* Function body *)
  let switch_stmt = A.(AilSswitch (mk_expr (AilEident param2_sym), mk_stmt (AilSblock ([], List.map generate_case ["GET"; "TAKE"])))) in
  let cast_expr_ = A.(AilEcast (empty_qualifiers, (mk_ctype C.(Pointer (empty_qualifiers, ctype))), mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), Id.id "ptr")))) in
  let deref_expr_ = A.(AilEunary (Indirection, mk_expr cast_expr_)) in
  let sct_opt = Sctypes.of_ctype ctype in
  let sct = match sct_opt with 
    | Some sct -> sct
    | None -> failwith "Bad sctype when trying to generate ownership function"
  in
  let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in 
  let ret_type = bt_to_ail_ctype bt in
  let return_stmt = A.(AilSreturn (mk_expr (add_conversion_fn deref_expr_ bt))) in
  (* Generating function declaration *)
  let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = (fn_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock ([], List.map mk_stmt [switch_stmt; return_stmt])))) in
  (decl, def)





(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
(* TODO: Use mu_datatypes from Mucore program instead of cn_datatypes *)
let rec cn_to_ail_expr_aux_internal 
: type a. (_ option) -> (_ option) -> (_ Cn.cn_datatype) list -> (C.union_tag * C.ctype) list -> IT.t -> a dest -> a
= fun const_prop pred_name dts globals (IT (term_, basetype, loc)) d ->
  match term_ with
  | Const const ->
    let ail_expr_ = cn_to_ail_const_internal const in
    dest d ([], [], mk_expr (add_conversion_fn ail_expr_ basetype))

  | Sym sym ->
      let sym = 
        if (String.equal (Sym.pp_string sym) "return") then
          Sym.fresh_pretty "return_cn"
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
      
      (* Check globals *)
      let global_match = List.filter (fun (global_sym, _) -> String.equal (Sym.pp_string sym) (Sym.pp_string global_sym)) globals in
      let ail_expr_ = match global_match with 
        | [] -> ail_expr_
        | (_, ctype) :: _ -> 
          let sct_opt = Sctypes.of_ctype ctype in 
          let sct = (match sct_opt with | Some t -> t | None -> failwith "Bad Sctype") in 
          let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in
          add_conversion_fn ail_expr_ bt
      in
      dest d ([], [], mk_expr ail_expr_)

  | Binop (bop, t1, t2) ->
    let b1, s1, e1 = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack in
    let b2, s2, e2 = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t2 PassBack in
    let (ail_bop, annot) = cn_to_ail_binop_internal (IT.basetype t1) (IT.basetype t2) bop in
    let strs = match annot with 
      | Some str -> [str]
      | None -> []
    in
    let default_ail_binop = A.AilEbinary (e1, ail_bop, e2) in

(*   
    let is_map it = 
      match IT.bt it with 
        | BT.Map (bt1, bt2) -> 
          Printf.printf "Type of %s: Map(%s, %s)\n" (str_of_it_ (IT.term it)) (str_of_ctype (bt_to_ail_ctype bt1)) (str_of_ctype (bt_to_ail_ctype bt2)); 
          true
        | _ -> false
    in *)

    

    let ail_expr_ = match ail_bop with 
      | A.Eq -> 
        (
          match IT.bt t1 with 
            | BT.Map (bt1, bt2) ->
              let (_, val_bt) = map_basetypes (IT.bt t1) in
              let val_ctype = bt_to_ail_ctype val_bt in
              let val_str = str_of_ctype val_ctype in
              let val_str = String.concat "_" (String.split_on_char ' ' val_str) in
              let val_equality_str =  val_str ^ "_equality" in
              A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_map_equality")), [e1; e2; mk_expr (AilEident (Sym.fresh_pretty val_equality_str))]))
            | _ -> 
              Printf.printf "ENTERED EQUALITY CASE\n";
              let ctype = (bt_to_ail_ctype (IT.bt t1)) in
              (match get_typedef_string ctype with 
                | Some str ->
                  Printf.printf "ENTERED SOME CASE\n";
                  let fn_name = str ^ "_equality" in 
                  A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [e1; e2]))
                | None -> 
                  Printf.printf "ENTERED NONE CASE\n";
                  (match rm_ctype ctype with 
                    | C.(Pointer (_, Ctype (_, Struct sym))) -> 
                      let dt_names = List.map (fun dt -> Sym.pp_string dt.cn_dt_name) dts in 
                      Printf.printf "ALL DATATYPE NAMES:\n";
                      List.iter (fun dt_str -> Printf.printf "%s\n" dt_str) dt_names;
                      Printf.printf "THIS STRUCT NAME: %s\n" (Sym.pp_string sym);
                      let is_datatype = List.mem String.equal (Sym.pp_string sym) dt_names in
                      let prefix = if is_datatype then "datatype_" else "struct_" in
                      let str = prefix ^ (String.concat "_" (String.split_on_char ' ' (Sym.pp_string sym))) in 
                      let fn_name = str ^ "_equality" in 
                      A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [e1; e2]))
                    | _ -> default_ail_binop))
        )
      | _ -> default_ail_binop
    in 
    dest d (b1 @ b2, s1 @ s2, mk_expr ~strs ail_expr_) 

  | Unop (unop, t) -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack in
    let (ail_unop, annot)  = cn_to_ail_unop_internal unop in
    let strs = match annot with 
      | Some str -> [str]
      | None -> []
    in
    let ail_expr_ = A.(AilEunary (ail_unop, e)) in 
    dest d (b, s, mk_expr ~strs ail_expr_)

  | SizeOf sct ->
    let ail_expr_ = A.(AilEsizeof (empty_qualifiers, Sctypes.to_ctype sct)) in 
    let ail_call_ = add_conversion_fn ail_expr_ BT.Integer in 
    dest d ([], [], mk_expr ail_call_)
  | OffsetOf _ -> failwith "TODO OffsetOf"

  | ITE (t1, t2, t3) -> 
    let b1, s1, e1 = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack in
    let b2, s2, e2 = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t2 PassBack in
    let b3, s3, e3 = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t3 PassBack in
    let ail_expr_ = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_ite")), [e1; e2; e3])) in
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
    let translated_t = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack in

    let (bs, ss, e) = gen_bool_while_loop sym start_int_const (mk_expr while_cond) translated_t in
    dest d (bs, ss, e)

  (* add Z3's Distinct for separation facts  *)
  | Tuple ts -> failwith "TODO1"
  | NthTuple (i, t) -> failwith "TODO2"
  | Struct (tag, ms) -> failwith "TODO3"

  | RecordMember (t, m) ->
    (* Currently assuming records only exist  *)
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack in
    let ail_expr_ = match pred_name with
      | Some sym -> A.(AilEmemberofptr (e, m))
      | None -> A.(AilEmemberof (e, m))
    in
    dest d (b, s, mk_expr ail_expr_)

  | StructMember (t, m) -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack in
    let ail_expr_ = A.(AilEmemberofptr (e, m)) in
    dest d (b, s, mk_expr ail_expr_)

  | StructUpdate ((struct_term, m), new_val) ->
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals struct_term PassBack in
    let (b2, s2, e2) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals new_val PassBack in
    let ail_memberof = A.(AilEmemberof (e1, m)) in
    let ail_assign = A.(AilSexpr (mk_expr (AilEassign ((mk_expr ail_memberof, e2))))) in
    dest d (b1 @ b2, s1 @ s2 @ [ail_assign], e1)

    (* Allocation *)
  | Record ms -> 
    (* Could either be (1) standalone record or (2) part of datatype. Case (2) may not exist soon *)
    (* Might need to pass records around like datatypes *)

    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in

    let generate_ail_stat (id, it) = 
      let (b, s, e) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack in
      let ail_memberof = A.(AilEmemberofptr (mk_expr res_ident, id)) in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (mk_expr ail_memberof, e)))) in
      (b, s, assign_stat)
    in

    let (b, s) = match pred_name with 
      (* Assuming records only get instantiated at point of return for predicates *)
      | Some sym -> 
          let sym_name = generate_sym_with_suffix ~suffix:"_record" sym in
          let ctype_ = C.(Pointer (empty_qualifiers, (mk_ctype (Struct sym_name)))) in
          let res_binding = create_binding res_sym (mk_ctype ctype_) in
          let fn_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (AilEsizeof (empty_qualifiers, mk_ctype C.(Struct sym_name)))])) in
          let alloc_stat = A.(AilSdeclaration [(res_sym, Some (mk_expr fn_call))]) in
          ([res_binding], [alloc_stat])
      | None -> ([], [])
    in
    
    let (bs, ss, assign_stats) = list_split_three (List.map generate_ail_stat ms) in
    dest d (List.concat bs @ b, List.concat ss @ s @ assign_stats, mk_expr res_ident)

  | RecordUpdate ((t1, m), t2) -> failwith "TODO6"

  (* Allocation *)
  | Constructor (sym, ms) -> 
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
    let res_sym = Sym.fresh () in
    let res_ident = A.(AilEident res_sym) in
    let ctype_ = C.(Pointer (empty_qualifiers, (mk_ctype (Struct parent_dt.cn_dt_name)))) in
    let res_binding = create_binding res_sym (mk_ctype ctype_) in
    let fn_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (AilEsizeof (empty_qualifiers, mk_ctype C.(Struct parent_dt.cn_dt_name)))])) in
    let ail_decl = A.(AilSdeclaration [(res_sym, Some (mk_expr fn_call))]) in

    let lc_constr_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true sym in 

    let generate_ail_stat (id, it) = 
      let (b, s, e) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals it PassBack in
      let ail_memberof = if (Id.equal id (Id.id "tag")) then e else 
        let e_ = A.(AilEmemberofptr (mk_expr res_ident, Id.id "u")) in
        let e_' = A.(AilEmemberof (mk_expr e_, create_id_from_sym lc_constr_sym)) in
        let e_'' = A.(AilEmemberofptr (mk_expr e_', id)) in
        mk_expr e_''
      in
      let assign_stat = A.(AilSexpr (mk_expr (AilEassign (ail_memberof, e)))) in
      (b, s, assign_stat)
    in

    let (bs, ss, assign_stats) = list_split_three (List.map generate_ail_stat ms) in

    let uc_constr_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true sym in
    let tag_member_ptr = A.(AilEmemberofptr (mk_expr res_ident, Id.id "tag")) in
    let tag_assign = A.(AilSexpr (mk_expr (AilEassign (mk_expr tag_member_ptr, mk_expr (AilEident uc_constr_sym))))) in

    dest d ((List.concat bs) @ [res_binding], [ail_decl; tag_assign] @ (List.concat ss) @ assign_stats, mk_expr res_ident)


  | MemberShift (_, tag, member) -> 
    let ail_expr_ = A.(AilEoffsetof (C.(Ctype ([], Struct tag)), member)) in
    dest d ([], [], mk_expr ail_expr_)

  | ArrayShift _ -> failwith "TODO7"
  | CopyAllocId _ -> failwith "TODO CopyAllocId"
  | Nil bt -> failwith "TODO8"
  | Cons (x, xs) -> failwith "TODO9"
  | Head xs -> 
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts globals xs PassBack in
    (* dereference to get first value, where xs is assumed to be a pointer *)
    let ail_expr_ = A.(AilEunary (Indirection, e)) in 
    dest d (b, s, mk_expr ail_expr_)

  | Tail xs -> failwith "TODO11"
  | NthList (t1, t2, t3) -> failwith "TODO12"
  | ArrayToList (t1, t2, t3) -> failwith "TODO13"
  | Representable (ct, t) -> failwith "TODO14"
  | Good (ct, t) -> 
    dest d ([], [], mk_expr true_const)
    (* cn_to_ail_expr_aux_internal const_prop pred_name dts globals t d *)
    
  | Aligned t_and_align -> failwith "TODO16"
  | WrapI (ct, t) -> 
    cn_to_ail_expr_aux_internal const_prop pred_name dts globals t d

  | MapConst (bt, t) -> failwith "TODO18"
  | MapSet (m, key, value) -> failwith "TODO19"
  | MapGet (m, key) ->
    (* Only works when index is a cn_integer *)
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals m PassBack in
    let (b2, s2, e2) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals key PassBack in
    let map_get_fcall = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_map_get")), [e1; e2])) in
    let (key_bt, val_bt) = BT.map_bt (IT.bt m) in 
    let ctype = bt_to_ail_ctype val_bt in 
    let cast_expr_ = A.(AilEcast (empty_qualifiers, ctype, mk_expr map_get_fcall)) in
    dest d (b1 @ b2, s1 @ s2, mk_expr cast_expr_)

  | MapDef ((sym, bt), t) -> failwith "TODO21"
  | Apply (sym, ts) ->
      let bs_ss_es = List.map (fun e -> cn_to_ail_expr_aux_internal const_prop pred_name dts globals e PassBack) ts in
      let (bs, ss, es) = list_split_three bs_ss_es in 
      let f = (mk_expr A.(AilEident sym)) in
      let ail_expr_ = A.AilEcall (f, es) in 
      (* let ail_expr_ = add_conversion_fn ail_expr_ basetype in  *)
      dest d (List.concat bs, List.concat ss, mk_expr ail_expr_)
      
  | Let ((var, t1), body) -> 
    let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t1 PassBack in
    let ctype = bt_to_ail_ctype (IT.bt t1) in
    let binding = create_binding var ctype in
    let ail_assign = A.(AilSdeclaration [(var, Some e1)]) in
    prefix d (b1 @ [binding], s1 @ [ail_assign]) (cn_to_ail_expr_aux_internal const_prop pred_name dts globals body d)

  | Match (t, ps) -> 
      Printf.printf "Reached pattern matching case\n";

      (* PATTERN COMPILER *)

      let mk_pattern pattern_ bt loc = T.(Pat (pattern_, bt, loc)) in

      let simplify_leading_variable t1 (ps, t2) =
        match ps with 
        | T.(Pat (PSym sym', p_bt, pt_loc)) :: ps' -> ((mk_pattern T.PWild p_bt pt_loc):: ps', T.(IT (Let ((sym', t1), t2), IT.basetype t2, pt_loc)))
        | p :: ps' -> (p :: ps', t2)
        | [] -> assert false
      in

      let leading_wildcard (ps, _) =
        match ps with
          | T.(Pat (PWild, _, _)) :: ps' -> true
          | _ :: ps' -> false
          | [] -> failwith "Empty patterns not allowed"
      in

      let expand_datatype c (ps, e) = 
        match ps with 
        | T.(Pat (PWild, p_bt, p_loc) as pat) :: ps' -> Some (pat :: ps', e)
        | T.(Pat (PConstructor (c_nm, members), _, _)) :: ps' ->
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
                      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t Assert
                    | Return -> 
                      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t Return
                    | AssignVar x -> 
                      cn_to_ail_expr_aux_internal const_prop pred_name dts globals t (AssignVar x)
                    | PassBack -> 
                      failwith "TODO Pattern Match PassBack")
                in 
                (bs, ss)
              | [] -> failwith "Incomplete pattern match"
              | ((_::_), e) :: rest -> failwith "Redundant patterns")

            | term :: vs -> 
              
              let cases = List.map (simplify_leading_variable term) cases in

              if List.for_all leading_wildcard cases then
                let cases = List.map (fun (ps, e) -> (List.tl ps, e)) cases in
                let (bindings', stats') = translate count vs cases in 
                (bindings', stats')
              else
                match IT.bt term with
                  | BT.Datatype sym -> 
                      let cn_dt = List.filter (fun dt -> String.equal (Sym.pp_string sym) (Sym.pp_string dt.cn_dt_name)) dts in 
                      (match cn_dt with 
                        | [] -> failwith "Datatype not found"
                        | dt :: _ ->
                          let (b1, s1, e1) = cn_to_ail_expr_aux_internal const_prop pred_name dts globals term PassBack in
                          let build_case (constr_sym, members_with_types) = 
                            let cases' = List.filter_map (expand_datatype constr_sym) cases in 
                            let suffix = "_" ^ (string_of_int count) in
                            let lc_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true constr_sym in 
                            let count_sym = generate_sym_with_suffix ~suffix ~lowercase:true constr_sym in 
                            let rhs_memberof_ptr = A.(AilEmemberofptr (e1, Id.id "u")) in (* TODO: Remove hack *)
                            let rhs_memberof = A.(AilEmemberof (mk_expr rhs_memberof_ptr, create_id_from_sym lc_sym)) in
                            let constr_binding = create_binding count_sym (mk_ctype C.(Pointer (empty_qualifiers, (mk_ctype C.(Struct lc_sym))))) in
                            let constructor_var_assign = mk_stmt A.(AilSdeclaration [(count_sym, Some (mk_expr rhs_memberof))]) in

                            let (ids, ts) = List.split members_with_types in
                            let bts = List.map cn_base_type_to_bt ts in
                            let new_constr_it = IT.IT (Sym count_sym, BT.Struct lc_sym, Cerb_location.unknown) in
                            let vars' = List.map (fun id -> T.StructMember (new_constr_it, id)) ids in
                            let terms' = List.map (fun (var', bt') -> T.IT (var', bt', Cerb_location.unknown)) (List.combine vars' bts) in

                            let (bindings, member_stats) = translate (count + 1) (terms' @ vs) cases' in
                            (* TODO: Check *)
                            let stat_block = A.AilSblock (constr_binding :: bindings, constructor_var_assign :: (List.map mk_stmt member_stats)) in
                            let tag_sym = generate_sym_with_suffix ~suffix:"" ~uppercase:true constr_sym in
                            let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, Sym.pp_string tag_sym); attr_args = []} in
                            let ail_case = A.(AilScase (Nat_big_num.zero (* placeholder *), mk_stmt stat_block)) in
                            A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case))
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
    let b, s, e = cn_to_ail_expr_aux_internal const_prop pred_name dts globals t PassBack in
    let ail_expr_ = match ((get_typedef_string (bt_to_ail_ctype bt)), get_typedef_string (bt_to_ail_ctype (IT.bt t))) with 
      | Some cast_type_str, Some original_type_str -> 
        let fn_name = "cast_" ^ original_type_str ^ "_to_" ^ cast_type_str in 
        A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty fn_name)), [e]))
      | _, _ ->
      A.(AilEcast (empty_qualifiers, (bt_to_ail_ctype bt), e)) in 
    dest d (b, s, mk_expr ail_expr_)


let cn_to_ail_expr_internal
  : type a. (_ Cn.cn_datatype) list -> (C.union_tag * C.ctype) list -> IT.t -> a dest -> a
  = fun dts globals cn_expr d ->
    cn_to_ail_expr_aux_internal None None dts globals cn_expr d

let cn_to_ail_expr_internal_with_pred_name
  : type a. (Sym.sym option) -> (_ Cn.cn_datatype) list -> (C.union_tag * C.ctype) list -> IT.t -> a dest -> a
    = fun pred_name_opt dts globals cn_expr d ->
      cn_to_ail_expr_aux_internal None pred_name_opt dts globals cn_expr d    


let create_member (ctype, id) =
  (id, (empty_attributes, None, empty_qualifiers, ctype))


let generate_tag_definition dt_members = 
  let ail_dt_members = List.map (fun (id, cn_type) -> (cn_to_ail_base_type cn_type, id)) dt_members in
  (* TODO: Check if something called tag already exists *)
  let members = List.map create_member ail_dt_members in
  C.(StructDef (members, None))

let generate_struct_definition ?(lc=true) (constructor, members) = 
  let constr_sym = if lc then
    Sym.fresh_pretty (String.lowercase_ascii (Sym.pp_string constructor))
  else
  constructor 
  in
  (constr_sym, (Cerb_location.unknown, empty_attributes, generate_tag_definition members))


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
  let enum = (enum_sym, (Cerb_location.unknown, attrs, enum_tag_definition)) in
  let cntype_sym = Sym.fresh_pretty "cntype" in

  let cntype_pointer = C.(Pointer (empty_qualifiers, mk_ctype (Struct cntype_sym))) in
  let extra_members tag_type = [
      (create_member (mk_ctype tag_type, Id.id "tag"));
      (create_member (mk_ctype cntype_pointer, Id.id "cntype"))]
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
    create_member (mk_ctype C.(Pointer (empty_qualifiers, (mk_ctype (Struct lc_sym)))), create_id_from_sym ~lowercase:true sym)) constructor_syms in
  let union_def = C.(UnionDef union_def_members) in
  let union_member = create_member (mk_ctype C.(Union union_sym), Id.id "u") in

  let structs = structs @ [(union_sym, (Cerb_location.unknown, empty_attributes, union_def)); (cn_datatype.cn_dt_name, (Cerb_location.unknown, empty_attributes, C.(StructDef ((extra_members (C.(Basic (Integer (Enum enum_sym))))) @ [union_member], None))))] in
  enum :: structs

let generate_datatype_equality_function (cn_datatype : cn_datatype) =
  (* 
    type cn_datatype 'a = <|
      cn_dt_loc: Loc.t;
      cn_dt_name: 'a;
      cn_dt_cases: list ('a * list (cn_base_type 'a * Symbol.identifier));
    |>   
  *)
  let dt_sym = cn_datatype.cn_dt_name in
  let fn_sym = Sym.fresh_pretty ("struct_" ^ (Sym.pp_string dt_sym) ^ "_equality") in
  let param1_sym = Sym.fresh_pretty "x" in 
  let param2_sym = Sym.fresh_pretty "y" in
  let id_tag = Id.id "tag" in
  let param_syms = [param1_sym; param2_sym] in 
  let param_type = (empty_qualifiers, mk_ctype (C.Pointer (empty_qualifiers, mk_ctype (Struct dt_sym))), false) in
  let tag_check_cond = A.(AilEbinary (mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), id_tag)), Ne, mk_expr (AilEmemberofptr (mk_expr (AilEident param2_sym), id_tag)))) in
  let false_it = IT.(IT (Const (Z (Z.of_int 0)), BT.Bool, Cerb_location.unknown)) in 
  (* Adds conversion function *)
  let (_, _, e1) = cn_to_ail_expr_internal [] [] false_it PassBack in
  let return_false = A.(AilSreturn e1) in
  let rec generate_equality_expr members sym1 sym2 = match members with 
    | [] -> 
      IT.(IT (Const (Z (Z.of_int 1)), BT.Bool, Cerb_location.unknown)) 
    | (id, cn_bt) :: ms -> 
      let sym1_it = IT.(IT (Sym sym1, BT.Loc, Cerb_location.unknown)) in 
      let sym2_it = IT.(IT (Sym sym2, BT.Loc, Cerb_location.unknown)) in
      let lhs = IT.(IT (StructMember (sym1_it, id), cn_base_type_to_bt cn_bt, Cerb_location.unknown)) in 
      let rhs = IT.(IT (StructMember (sym2_it, id), cn_base_type_to_bt cn_bt, Cerb_location.unknown)) in 
      let eq_it = IT.(IT (Binop (EQ, lhs, rhs), BT.Bool, Cerb_location.unknown)) in
      let remaining = generate_equality_expr ms sym1 sym2 in 
      IT.(IT (Binop (And, eq_it, remaining), BT.Bool, Cerb_location.unknown))
  in
  let create_case (constructor, members) =
    let enum_str = Sym.pp_string (generate_sym_with_suffix ~suffix:"" ~uppercase:true constructor) in
    let attribute : CF.Annot.attribute = {attr_ns = None; attr_id = CF.Symbol.Identifier (Cerb_location.unknown, enum_str); attr_args = []} in 
    let x_constr_sym = Sym.fresh () in 
    let y_constr_sym = Sym.fresh () in
    let constr_syms = [x_constr_sym; y_constr_sym] in
    let (bs, ss) = match members with 
    | [] -> ([], [])
    | _ -> 
        let lc_constr_sym = generate_sym_with_suffix ~suffix:"" ~lowercase:true constructor in
        let constr_id = create_id_from_sym ~lowercase:true constructor in 
        let constr_struct_type = mk_ctype C.(Pointer (empty_qualifiers, mk_ctype (Struct lc_constr_sym))) in
        let bindings = List.map (fun sym -> create_binding sym constr_struct_type) constr_syms in 
        let memberof_ptr_es = List.map (fun sym -> mk_expr A.(AilEmemberofptr (mk_expr (AilEident sym), Id.id "u"))) param_syms in
        let decls = List.map (fun (constr_sym, e) -> A.(AilSdeclaration [(constr_sym, Some (mk_expr (AilEmemberof (e, constr_id))))])) (List.combine constr_syms memberof_ptr_es) in
        (bindings, List.map mk_stmt decls)
    in
    let equality_expr = generate_equality_expr members x_constr_sym y_constr_sym in
    let (_, _, e) = cn_to_ail_expr_internal [] [] equality_expr PassBack in
    let return_stat = mk_stmt A.(AilSreturn e) in
    let ail_case = A.(AilScase (Nat_big_num.zero, mk_stmt (AilSblock (bs, ss @ [return_stat])))) in 
    A.(AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [attribute], ail_case))
  in
  let switch_stmt = A.(AilSswitch (mk_expr (AilEmemberofptr (mk_expr (AilEident param1_sym), id_tag)), mk_stmt (AilSblock ([], List.map create_case cn_datatype.cn_dt_cases)))) in
  let tag_if_stmt = A.(AilSif (mk_expr tag_check_cond, mk_stmt return_false, mk_stmt switch_stmt)) in
  let ret_type = bt_to_ail_ctype BT.Bool in
  (* Generating function declaration *)
  let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), [param_type; param_type], false, false, false)))) in
  (* Generating function definition *)
  let def = (fn_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock ([], [mk_stmt tag_if_stmt])))) in
  [(decl, def)]

let generate_struct_equality_function ((sym, (loc, attrs, tag_def)) : (A.ail_identifier * (Cerb_location.t * CF.Annot.attributes * C.tag_definition))) = match tag_def with 
    | C.StructDef (members, _) -> 
      let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in 
      let cn_struct_ctype = mk_ctype C.(Struct cn_sym) in
      let cn_struct_ptr_ctype = mk_ctype C.(Pointer (empty_qualifiers, cn_struct_ctype)) in
      let fn_sym = Sym.fresh_pretty ("struct_" ^ (Sym.pp_string cn_sym) ^ "_equality") in
      let param_syms = [Sym.fresh_pretty "x"; Sym.fresh_pretty "y"] in 
      let param_type = (empty_qualifiers, mk_ctype (C.Pointer (empty_qualifiers, mk_ctype Void)), false) in
      let cast_param_syms = List.map (fun sym -> generate_sym_with_suffix ~suffix:"_cast" sym) param_syms in 
      let cast_bindings = List.map (fun sym -> create_binding sym cn_struct_ptr_ctype) cast_param_syms in 
      let cast_assignments = List.map (fun (cast_sym, sym) -> A.(AilSdeclaration [cast_sym, Some (mk_expr (AilEcast (empty_qualifiers, cn_struct_ptr_ctype, (mk_expr (AilEident sym)))))])) (List.combine cast_param_syms param_syms) in 
      (* Function body *)
      let generate_member_equality (id, (_, _, _, ctype)) = 
        let doc = (CF.Pp_ail.pp_ctype ~executable_spec:true empty_qualifiers ctype) in 
        Printf.printf "%s\n" (CF.Pp_utils.to_plain_pretty_string doc);
        let sct_opt = Sctypes.of_ctype ctype in 
        let sct = match sct_opt with 
          | Some t -> t
          | None -> 
            Printf.printf "None case\n";
            failwith "Bad sctype"
        in
        let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in 
        let typedef_str = match get_typedef_string (bt_to_ail_ctype bt) with 
          | Some str -> String.concat "_" (String.split_on_char ' ' str)
          | None -> match rm_ctype ctype with 
            | C.Struct struct_sym -> "struct_" ^ (Sym.pp_string struct_sym)
            | _ -> ""
        in
        let equality_fun_str = typedef_str ^ "_equality" in
        let args = List.map (fun cast_sym -> mk_expr (AilEmemberofptr (mk_expr (AilEident cast_sym), id))) cast_param_syms in 
        mk_expr A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty equality_fun_str)), args))
      in
      let member_equality_exprs = List.map generate_member_equality members in 
      let cn_bool_and_sym = Sym.fresh_pretty "cn_bool_and" in
      let ail_and_binop = List.fold_left (fun e1 e2 -> mk_expr (A.(AilEcall (mk_expr (AilEident cn_bool_and_sym), [e1; e2])))) (mk_expr (add_conversion_fn true_const BT.Bool)) member_equality_exprs in
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
      let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), [param_type; param_type], false, false, false)))) in
      (* Generating function definition *)
      let def = (fn_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (cast_bindings, List.map mk_stmt (cast_assignments @ [return_stmt]))))) in
      [(decl, def)]
  | C.UnionDef _ -> []

let generate_struct_conversion_function ((sym, (loc, attrs, tag_def)) : (A.ail_identifier * (Cerb_location.t * CF.Annot.attributes * C.tag_definition))) = match tag_def with 
  | C.StructDef (members, _) -> 
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in 
    let cn_struct_ctype = mk_ctype C.(Struct cn_sym) in
    let fn_sym = Sym.fresh_pretty ("convert_to_struct_" ^ (Sym.pp_string cn_sym)) in
    let param_sym = sym in
    let param_type = (empty_qualifiers, mk_ctype (C.(Struct sym)), false) in
    (* Function body *)
    let res_sym = Sym.fresh_pretty "res" in 
    let res_binding = create_binding res_sym (mk_ctype (C.Pointer (empty_qualifiers, cn_struct_ctype))) in
    let alloc_fcall = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "alloc")), [mk_expr (AilEsizeof (empty_qualifiers, cn_struct_ctype))])) in 
    let res_assign = A.(AilSdeclaration [(res_sym, Some (mk_expr alloc_fcall))]) in 
    let generate_member_assignment (id, (_, _, _, ctype)) = 
      let rhs = A.(AilEmemberof (mk_expr (AilEident param_sym), id)) in
      let sct_opt = Sctypes.of_ctype ctype in 
      let sct = match sct_opt with 
        | Some t -> t
        | None -> failwith "Bad sctype"
      in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in 
      let rhs = add_conversion_fn rhs bt in 
      let lhs = A.(AilEmemberofptr (mk_expr (AilEident res_sym), id)) in 
      A.(AilSexpr (mk_expr (AilEassign (mk_expr lhs, mk_expr rhs))))
    in
    let member_assignments = List.map generate_member_assignment members in 
    let return_stmt = A.(AilSreturn (mk_expr (AilEident res_sym))) in 
    let ret_type = (bt_to_ail_ctype (BT.Struct sym)) in
    (* Generating function declaration *)
    let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), [param_type], false, false, false)))) in
    (* Generating function definition *)
    let def = (fn_sym, (Cerb_location.unknown, 0, empty_attributes, [param_sym], mk_stmt A.(AilSblock ([res_binding], List.map mk_stmt (res_assign :: member_assignments @ [return_stmt]))))) in
    [(decl, def)]
  | C.UnionDef _ -> []


let cn_to_ail_struct ((sym, (loc, attrs, tag_def)) : (A.ail_identifier * (Cerb_location.t * CF.Annot.attributes * C.tag_definition))) = match tag_def with 
  | C.StructDef (members, opt) -> 
    let cn_struct_sym = generate_sym_with_suffix ~suffix:"_cn" sym in
    let new_members = List.map (fun (id, (attrs, alignment, qualifiers, ctype)) -> 
      let sct_opt = Sctypes.of_ctype ctype in 
      let sct = match sct_opt with | Some t -> t | None -> failwith "Bad sctype" in
      let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in 
      (id, (attrs, alignment, qualifiers, (bt_to_ail_ctype bt))))
    members 
    in
    [(cn_struct_sym, (loc, attrs, C.StructDef (new_members, opt)))]
  | C.UnionDef _ -> []

let cn_to_ail_resource_internal sym dts globals (preds : Mucore.T.resource_predicates) =
  let calculate_return_type = function 
  | ResourceTypes.Owned (sct, _) -> (Sctypes.to_ctype sct, BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct)
  | PName pname -> 
    let matching_preds = List.filter (fun (pred_sym', def) -> String.equal (Sym.pp_string pname) (Sym.pp_string pred_sym')) preds in
    let (pred_sym', pred_def') = match matching_preds with 
      | [] -> failwith "Predicate not found"
      | p :: _ -> p
    in 
    let cn_bt = bt_to_cn_base_type pred_def'.oarg_bt in
    let ctype = match cn_bt with 
      | CN_record _ ->
        let pred_record_name = generate_sym_with_suffix ~suffix:"_record" pred_sym' in
        mk_ctype C.(Pointer (empty_qualifiers, (mk_ctype (Struct pred_record_name))))
      | _ -> cn_to_ail_base_type ~pred_sym:(Some pred_sym') cn_bt
    in 
    (ctype, pred_def'.oarg_bt)
  in
  (* let make_deref_expr_ e_ = A.(AilEunary (Indirection, mk_expr e_)) in  *)
  function
  | ResourceTypes.P p -> 
    let (ctype, bt) = calculate_return_type p.name in

    let (b, s, e) = cn_to_ail_expr_internal dts globals p.pointer PassBack in
    let (rhs, bs, ss, owned_ctype) = match p.name with 
      | Owned (sct, _) ->
        let sct_str = CF.Pp_utils.to_plain_pretty_string (Sctypes.pp sct) in 
        let sct_str = String.concat "_" (String.split_on_char ' ' sct_str) in
        let owned_fn_name = "owned_" ^ sct_str in 
        (* Hack with enum as sym *)
        let enum_sym = Sym.fresh_pretty "GET" in
        let enum_val_get = IT.(IT (Sym enum_sym, BT.Integer, Cerb_location.unknown)) in
        let fn_call_it = IT.IT (Apply (Sym.fresh_pretty owned_fn_name, [p.pointer; enum_val_get]), BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct, Cerb_location.unknown) in
        let (bs', ss', e') = cn_to_ail_expr_internal dts globals fn_call_it PassBack in
        let binding = create_binding sym (bt_to_ail_ctype bt) in
        (e', binding :: bs', ss', Some (Sctypes.to_ctype sct))
        (* let cast_ctype_pointer = C.(Pointer (empty_qualifiers, ctype)) in
        let cast_e_ = A.(AilEcast (empty_qualifiers, mk_ctype cast_ctype_pointer, e)) in
        (make_deref_expr_ cast_e_, [], []) *)
      | PName pname -> 
        let (bs, ss, es) = list_split_three (List.map (fun it -> cn_to_ail_expr_internal dts globals it PassBack) p.iargs) in
        let fcall = A.(AilEcall (mk_expr (AilEident pname), e :: es)) in
        let binding = create_binding sym (bt_to_ail_ctype ~pred_sym:(Some pname) bt) in
        (mk_expr fcall, binding :: (List.concat bs), List.concat ss, None)
    in
    let s_decl = match rm_ctype ctype with 
      | C.Void -> A.(AilSexpr rhs)
      | _ -> A.(AilSdeclaration [(sym, Some rhs)]) 
    in
    (b @ bs, s @ ss @ [s_decl], owned_ctype)

  | ResourceTypes.Q q -> 
    (* 
      Input is expr of the form:
      take sym = each (integer q.q; q.permission){ Owned(q.pointer + (q.q * q.step)) }
    *)
    let (b1, s1, e1) = cn_to_ail_expr_internal dts globals q.pointer PassBack in
    
    (*
    Generating a loop of the form:
    <set q.q to start value>
    while (q.permission) {
      *(sym + q.q * q.step) = *(q.pointer + q.q * q.step);
      q.q++;
    } 
    *)
      
    let i_sym = fst q.q in
    let start_expr = generate_start_expr (get_leftmost_and_expr q.permission) (fst q.q) in
    let (_, _, e_start) = cn_to_ail_expr_internal dts globals start_expr PassBack in 
    (* let (b_end, s_end, e_end) = cn_to_ail_expr_internal dts q.permission PassBack in *)
    let cn_integer_ptr_ctype = bt_to_ail_ctype BT.Integer in 
    (* let convert_to_cn_integer_sym = Sym.fresh_pretty "convert_to_cn_integer" in  *)
    
    let (b2, s2, e2) = cn_to_ail_expr_internal dts globals q.permission PassBack in
    let (b3, s3, e3) = cn_to_ail_expr_internal dts globals q.step PassBack in
    (* let conversion_fcall = A.(AilEcall (mk_expr (AilEident convert_to_cn_integer_sym), [e_start])) in *)

    let start_binding = create_binding i_sym cn_integer_ptr_ctype in
    let start_assign = A.(AilSdeclaration [(i_sym, Some e_start)]) in
    (* let (end_binding, end_assign) = convert_to_cn_binop e_end in  *)

    (* let q_times_step = A.(AilEbinary (mk_expr (AilEident i_sym), Arithmetic Mul, e3)) in *)
    (* let gen_add_expr_ e_ = 
      A.(AilEbinary (mk_expr e_, Arithmetic Add, mk_expr q_times_step))
    in *)
    (* let sym_add_expr = make_deref_expr_ (gen_add_expr_ A.(AilEident sym)) in *)

    let (return_ctype, return_bt) = calculate_return_type q.name in

    (* Translation of q.pointer *)
    let i_it = IT.IT (Terms.(Sym i_sym), BT.Integer, Cerb_location.unknown) in 
    let step_binop = IT.IT (Terms.(Binop (Mul, i_it, q.step)), BT.Integer, Cerb_location.unknown) in 
    let value_it = IT.IT (Terms.(Binop (Add, q.pointer, step_binop)), BT.Loc, Cerb_location.unknown) in
    let (b4, s4, e4) = cn_to_ail_expr_internal dts globals value_it PassBack in

    let ptr_add_sym = Sym.fresh () in
    let cn_pointer_return_type = bt_to_ail_ctype BT.Loc in 
    let ptr_add_binding = create_binding ptr_add_sym cn_pointer_return_type in
    let ptr_add_stat = A.(AilSdeclaration [(ptr_add_sym, Some e4)]) in

    let (rhs, bs, ss, owned_ctype) = match q.name with 
      | Owned (sct, _) -> 
        let sct_str = CF.Pp_utils.to_plain_pretty_string (Sctypes.pp sct) in 
        let sct_str = String.concat "_" (String.split_on_char ' ' sct_str) in
        let owned_fn_name = "owned_" ^ sct_str in 
        let ptr_add_it = IT.(IT (Sym ptr_add_sym, BT.Loc, Cerb_location.unknown)) in
        (* Hack with enum as sym *)
        let enum_sym = Sym.fresh_pretty "GET" in
        let enum_val_get = IT.(IT (Sym enum_sym, BT.Integer, Cerb_location.unknown)) in
        let fn_call_it = IT.IT (Apply (Sym.fresh_pretty owned_fn_name, [ptr_add_it; enum_val_get]), BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct, Cerb_location.unknown) in
        let (bs', ss', e') = cn_to_ail_expr_internal dts globals fn_call_it PassBack in
        (e', bs', ss', Some (Sctypes.to_ctype sct))
      | PName pname -> 
        let (bs, ss, es) = list_split_three (List.map (fun it -> cn_to_ail_expr_internal dts globals it PassBack) q.iargs) in
        let fcall = A.(AilEcall (mk_expr (AilEident pname), (mk_expr (AilEident ptr_add_sym)) :: es)) in
        (mk_expr fcall, List.concat bs, List.concat ss, None)
    in

    let increment_fn_sym = Sym.fresh_pretty "cn_integer_increment" in
    let increment_stat = A.(AilSexpr (mk_expr (AilEcall (mk_expr (AilEident increment_fn_sym), [mk_expr (AilEident i_sym)])))) in 

    let convert_from_cn_bool_ident = mk_expr A.(AilEident (Sym.fresh_pretty "convert_from_cn_bool")) in
    let e2_with_conversion = mk_expr A.(AilEcall (convert_from_cn_bool_ident, [e2])) in

    let (bs', ss') = match rm_ctype return_ctype with 
      | C.Void -> 
        let void_pred_call = A.(AilSexpr rhs) in
        let while_loop = A.(AilSwhile (e2_with_conversion, mk_stmt (AilSblock ([ptr_add_binding], List.map mk_stmt [ptr_add_stat; void_pred_call; increment_stat])), 0)) in
        let ail_block = A.(AilSblock ([], List.map mk_stmt ([start_assign; while_loop]))) in
        ([], [ail_block])
      | _ -> 
        let cn_map_type = mk_ctype ~annots:[CF.Annot.Atypedef (Sym.fresh_pretty "cn_map")] C.Void in
        let sym_binding = create_binding sym (mk_ctype C.(Pointer (empty_qualifiers, cn_map_type))) in
        let create_call = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "map_create")), [])) in
        let sym_decl = A.(AilSdeclaration [(sym, Some (mk_expr create_call))]) in
        let map_set_expr_ = A.(AilEcall (mk_expr (AilEident (Sym.fresh_pretty "cn_map_set")), (List.map mk_expr [AilEident sym; AilEident i_sym]) @ [rhs])) in
        let while_loop = A.(AilSwhile (e2_with_conversion, mk_stmt (AilSblock (ptr_add_binding :: b4, List.map mk_stmt (s4 @ [ptr_add_stat; (AilSexpr (mk_expr map_set_expr_)); increment_stat]))), 0)) in
        let ail_block = A.(AilSblock ([], List.map mk_stmt ([start_assign; while_loop]))) in
        ([sym_binding], [sym_decl; ail_block])
    in

    (b1 @ b2 @ b3 @ [start_binding] @ bs' @ bs, s1 @ s2 @ s3 @ ss @ ss', owned_ctype)

let cn_to_ail_logical_constraint_internal : type a. (_ Cn.cn_datatype) list -> (C.union_tag * C.ctype) list -> a dest -> LC.logical_constraint -> a
  = fun dts globals d lc -> 
      match lc with
        | LogicalConstraints.T it -> 
          cn_to_ail_expr_internal dts globals it d
        | LogicalConstraints.Forall ((sym, bt), it) -> 
          let (cond_it, t) = match IT.term it with 
            | Binop (Impl, it, it') -> (it, it')
            | _ -> failwith "Incorrect form of forall logical constraint term"
        in


        match IT.term t with 
          | Good _ -> dest d ([], [], mk_expr true_const)
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

          let start_expr = generate_start_expr (get_leftmost_and_expr cond_it) sym in
          let while_cond = get_rest_of_expr_r cond_it in
          let (b1, s1, e1) = cn_to_ail_expr_internal dts globals start_expr PassBack in
          let (b2, s2, e2) = cn_to_ail_expr_internal dts globals while_cond PassBack in
          
          let t_translated = cn_to_ail_expr_internal dts globals t PassBack in
          let (bs, ss, e) = gen_bool_while_loop sym (rm_expr e1) e2 t_translated in
          dest d (bs, ss, e)
          
    
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
let cn_to_ail_function_internal (fn_sym, (def : LogicalFunctions.definition)) cn_datatypes = 
  let ret_type = bt_to_ail_ctype ~pred_sym:(Some fn_sym) def.return_bt in
  (* let ret_type = mk_ctype C.(Pointer (empty_qualifiers, ret_type)) in *)
  let (bs, ail_func_body_opt) =
  match def.definition with
    | Def it
    | Rec_Def it ->
      let (bs, ss) = cn_to_ail_expr_internal_with_pred_name (Some fn_sym) cn_datatypes [] it Return in
      (bs, Some (List.map mk_stmt ss))
    | Uninterp -> ([], None)
  in
  let ail_record_opt = generate_record_opt fn_sym def.return_bt in
  let params = List.map (fun (sym, bt) -> (sym, (bt_to_ail_ctype bt))) def.args in
  let (param_syms, param_types) = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  (* Generating function declaration *)
  let decl = (fn_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = match ail_func_body_opt with 
    | Some ail_func_body -> Some (fn_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (bs, ail_func_body))))
    | None -> None
  in
  ((decl, def), ail_record_opt)


  
let rec cn_to_ail_lat_internal dts pred_sym_opt globals ownership_ctypes preds = function
  | LAT.Define ((name, it), info, lat) -> 
    let ctype = bt_to_ail_ctype (IT.bt it) in
    let binding = create_binding name ctype in
    let (b1, s1) = cn_to_ail_expr_internal_with_pred_name pred_sym_opt dts globals it (AssignVar name) in
    let (b2, s2, ownership_ctypes') = cn_to_ail_lat_internal dts pred_sym_opt globals ownership_ctypes preds lat in
    (b1 @ b2 @ [binding], s1 @ s2, ownership_ctypes')

  | LAT.Resource ((name, (ret, bt)), info, lat) -> 
    let (b1, s1, owned_ctype) = cn_to_ail_resource_internal name dts globals preds ret in
    let ct = match owned_ctype with 
      | Some t -> if List.mem C.ctypeEqual t ownership_ctypes then [] else [t]
      | None -> []
    in
    let (b2, s2, ownership_ctypes') = cn_to_ail_lat_internal dts pred_sym_opt globals (ct @ ownership_ctypes) preds lat in
    (b1 @ b2, s1 @ s2, ownership_ctypes')

  | LAT.Constraint (lc, (loc, str_opt), lat) -> 
    let (b1, s, e) = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    (* TODO: Check this logic *)
    let ss = match str_opt with 
      | Some info -> 
        (* Printf.printf "Logical constraint info: %s\n" info; *)
        []
      | None -> 
        (* Printf.printf "No logical constraint info\n"; *)
        let ail_stat_ = A.(AilSexpr (mk_expr (generate_cn_assert e))) in
        s @ [ail_stat_]
    in
    let (b2, s2, ownership_ctypes') = cn_to_ail_lat_internal dts pred_sym_opt globals ownership_ctypes preds lat in
    (b1 @ b2, ss @ s2, ownership_ctypes')

  | LAT.I it ->
    let (bs, ss) = cn_to_ail_expr_internal_with_pred_name pred_sym_opt dts globals it Return in 
    (bs, ss, ownership_ctypes)



let cn_to_ail_predicate_internal (pred_sym, (def : ResourcePredicates.definition)) dts globals ots preds = 
  let ret_type = bt_to_ail_ctype ~pred_sym:(Some pred_sym) def.oarg_bt in

  let rec clause_translate (clauses : RP.clause list) ownership_ctypes = 
    match clauses with
      | [] -> ([], [], ownership_ctypes)
      | c :: cs ->
        let (bs, ss, ownership_ctypes') = cn_to_ail_lat_internal dts (Some pred_sym) globals ownership_ctypes preds c.packing_ft in
        match c.guard with 
          | IT (Const (Bool true), _, _) -> 
            let (bs'', ss'', ownership_ctypes'') = clause_translate cs ownership_ctypes' in
            (bs @ bs'', ss @ ss'', ownership_ctypes'')
          | _ -> 
            let (b1, s1, e) = cn_to_ail_expr_internal_with_pred_name (Some pred_sym) dts [] c.guard PassBack in
            let (bs'', ss'', ownership_ctypes'') = clause_translate cs ownership_ctypes' in
            let ail_if_stat = A.(AilSif (e, mk_stmt (AilSblock (bs, List.map mk_stmt ss)), mk_stmt (AilSblock (bs'', List.map mk_stmt ss'')))) in
            ([], [ail_if_stat], ownership_ctypes'')
  in

  let (bs, ss, ownership_ctypes') = match def.clauses with 
    | Some clauses -> clause_translate clauses ots
    | None -> ([], [], ots)
  in

  let pred_body = List.map mk_stmt ss in

  let ail_record_opt = generate_record_opt pred_sym def.oarg_bt in
  let params = List.map (fun (sym, bt) -> (sym, (bt_to_ail_ctype bt))) ((def.pointer, BT.Loc) :: def.iargs) in
  let (param_syms, param_types) = List.split params in
  let param_types = List.map (fun t -> (empty_qualifiers, t, false)) param_types in
  (* Generating function declaration *)
  let decl = (pred_sym, (Cerb_location.unknown, empty_attributes, A.(Decl_function (false, (empty_qualifiers, ret_type), param_types, false, false, false)))) in
  (* Generating function definition *)
  let def = (pred_sym, (Cerb_location.unknown, 0, empty_attributes, param_syms, mk_stmt A.(AilSblock (bs, pred_body)))) in
  ((decl, def), ail_record_opt, ownership_ctypes')

let rec cn_to_ail_predicates_internal pred_def_list dts globals ots preds = 
  match pred_def_list with 
    | [] -> ([], [], ots)
    | p :: ps ->
      let (d, r, ots') = cn_to_ail_predicate_internal p dts globals ots preds in 
      let (ds, rs, ots'') = cn_to_ail_predicates_internal ps dts globals ots' preds in 
      (d :: ds, r :: rs, ots'')


(* TODO: Add destination passing? *)
let rec cn_to_ail_post_aux_internal dts globals ownership_ctypes preds = function
  | LRT.Define ((name, it), info, t) ->
    Printf.printf "LRT.Define\n";
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in 
    let new_lrt = Core_to_mucore.fn_spec_instrumentation_sym_subst_lrt (name, IT.bt it, new_name) t in 
    let binding = create_binding new_name (bt_to_ail_ctype (IT.bt it)) in
    let (b1, s1) = cn_to_ail_expr_internal dts globals it (AssignVar new_name) in
    let (b2, s2, ownership_ctypes') = cn_to_ail_post_aux_internal dts globals ownership_ctypes preds new_lrt in
    (b1 @ b2 @ [binding], s1 @ s2, ownership_ctypes')

  | LRT.Resource ((name, (re, bt)), info, t)  ->
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in 
    let (b1, s1, owned_ctype) = cn_to_ail_resource_internal new_name dts globals preds re in
    (* No duplicates *)
    let ct = match owned_ctype with 
      | Some t -> if List.mem C.ctypeEqual t ownership_ctypes then [] else [t]
      | None -> []
    in
    let new_lrt = Core_to_mucore.fn_spec_instrumentation_sym_subst_lrt (name, bt, new_name) t in 
    let (b2, s2, ownership_ctypes') = cn_to_ail_post_aux_internal dts globals (ct @ ownership_ctypes) preds new_lrt in
    (b1 @ b2, s1 @ s2, ownership_ctypes')

  | LRT.Constraint (lc, (loc, str_opt), t) -> 
    let (b1, s, e) = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    (* TODO: Check this logic *)
    let ss = match str_opt with 
      | Some info -> 
        []
      | None -> 
        let ail_stat_ = A.(AilSexpr (mk_expr (generate_cn_assert e))) in
        s @ [ail_stat_]
    in
    let (b2, s2, ownership_ctypes') = cn_to_ail_post_aux_internal dts globals ownership_ctypes preds t in

    (b1 @ b2, ss @ s2, ownership_ctypes')

  | LRT.I -> ([], [], ownership_ctypes)


let cn_to_ail_post_internal dts globals ownership_ctypes preds (RT.Computational (bound, oinfo, t)) = 
  let (bs, ss, ownership_ctypes') = cn_to_ail_post_aux_internal dts globals ownership_ctypes preds t in 
  (bs, List.map mk_stmt ss, ownership_ctypes')

(* TODO: Add destination passing *)
let cn_to_ail_cnstatement_internal : type a. (_ Cn.cn_datatype) list -> (C.union_tag * C.ctype) list -> a dest -> Cnprog.cn_statement -> (a * bool)
= fun dts globals d cnstatement ->
  let true_it = IT.IT (Const (Bool true), BT.Bool, Cerb_location.unknown) in
  let default_true_res = cn_to_ail_expr_internal dts globals true_it d in
  match cnstatement with
  | Cnprog.M_CN_pack_unpack (pack_unpack, pt) -> 
    (default_true_res, true)

  | Cnprog.M_CN_have lc -> failwith "TODO M_CN_have"

  | Cnprog.M_CN_instantiate (to_instantiate, it) -> 
    Printf.printf "Translating CN instantiate\n";
    (default_true_res, true)
  | Cnprog.M_CN_split_case _ -> failwith "TODO M_CN_split_case"


  | Cnprog.M_CN_extract (_, _, it) -> 
    Printf.printf "Translating CN extract\n";
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
    (cn_to_ail_logical_constraint_internal dts globals d lc, false)

  | Cnprog.M_CN_inline _ -> failwith "TODO M_CN_inline"
  | Cnprog.M_CN_print _ -> failwith "TODO M_CN_print"


let rec cn_to_ail_cnprog_internal_aux dts globals = function
| Cnprog.M_CN_let (loc, (name, {ct; pointer}), prog) -> 
  
  let (b1, s, e) = cn_to_ail_expr_internal dts globals pointer PassBack in
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
    | C.(Pointer (_, ct)) -> ct
    | ct_' -> mk_ctype ct_'
  in
  let binding = create_binding name ct_without_ptr in
 
  let ail_stat_ = A.(AilSdeclaration [(name, Some (mk_expr ail_deref_expr_))]) in
  let ((b2, ss), no_op) = cn_to_ail_cnprog_internal_aux dts globals prog in
  (* let ail_stat_ = A.(AilSexpr (mk_expr (AilEassign (mk_expr (AilEident name), mk_expr ail_deref_expr_)))) in *)
  if no_op then 
    (([], []), true)
  else 
    ((b1 @ binding :: b2, s @ ail_stat_ :: ss), false) 

  (* if no_op then
    ((loc', [], []), true)
  else
    ((loc', b1 @ b2 @ [binding], s @ ail_stat_ :: ss), false) *)

| Cnprog.M_CN_statement (loc, stmt) ->
  let ((bs, ss), no_op) = cn_to_ail_cnstatement_internal dts globals Assert stmt in 
  ((bs, ss), no_op)

let cn_to_ail_cnprog_internal dts globals cn_prog = 
  let ((bs, ss), _) = cn_to_ail_cnprog_internal_aux dts globals cn_prog in 
  (bs, ss)

let cn_to_ail_statements dts globals (loc, cn_progs) = 
  let bs_and_ss = List.map (fun prog -> cn_to_ail_cnprog_internal dts globals prog) cn_progs in 
  let (bs, ss) = List.split bs_and_ss in 
  (loc, (List.concat bs, List.concat ss))

let prepend_to_precondition ail_executable_spec (b1, s1) = 
  let (b2, s2) = ail_executable_spec.pre in
  {ail_executable_spec with pre = (b1 @ b2, s1 @ s2)}

let rec cn_to_ail_lat_internal_2 dts globals ownership_ctypes preds c_return_type = function
  | LAT.Define ((name, it), info, lat) -> 
    let ctype = bt_to_ail_ctype (IT.bt it) in
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in 
    let new_lat = Core_to_mucore.fn_spec_instrumentation_sym_subst_lat (name, IT.bt it, new_name) lat in 
    (* let ctype = mk_ctype C.(Pointer (empty_qualifiers, ctype)) in *)
    let binding = create_binding new_name ctype in
    let (b1, s1) = cn_to_ail_expr_internal dts globals it (AssignVar new_name) in
    let ail_executable_spec = cn_to_ail_lat_internal_2 dts globals ownership_ctypes preds c_return_type new_lat in
    prepend_to_precondition ail_executable_spec (binding :: b1, s1)

  | LAT.Resource ((name, (ret, bt)), info, lat) -> 
    let new_name = generate_sym_with_suffix ~suffix:"_cn" name in 
    let (b1, s1, owned_ctype) = cn_to_ail_resource_internal new_name dts globals preds ret in
    let ct = match owned_ctype with 
      | Some t -> if List.mem C.ctypeEqual t ownership_ctypes then [] else [t]
      | None -> []
    in
    let new_lat = Core_to_mucore.fn_spec_instrumentation_sym_subst_lat (name, bt, new_name) lat in 
    let ail_executable_spec = cn_to_ail_lat_internal_2 dts globals (ct @ ownership_ctypes) preds c_return_type new_lat in
    prepend_to_precondition ail_executable_spec (b1, s1)

  | LAT.Constraint (lc, (loc, str_opt), lat) -> 
    let (b1, s, e) = cn_to_ail_logical_constraint_internal dts globals PassBack lc in
    (* TODO: Check this logic *)
    let ss = match str_opt with 
      | Some info -> 
        (* Printf.printf "Logical constraint info: %s\n" info; *)
        []
      | None -> 
        (* Printf.printf "No logical constraint info\n"; *)
        let ail_stat_ = A.(AilSexpr (mk_expr (generate_cn_assert e))) in
        s @ [ail_stat_]
    in
    let ail_executable_spec = cn_to_ail_lat_internal_2 dts globals ownership_ctypes preds c_return_type lat in
    prepend_to_precondition ail_executable_spec (b1, ss)

  | LAT.I (post, stats) ->
     let rec remove_duplicates locs stats = 
      (match stats with 
        | [] -> []
        | (loc, s) :: ss ->
          let loc_equality x y = 
            String.equal (Cerb_location.location_to_string x) (Cerb_location.location_to_string y) in 
          if (List.mem loc_equality loc locs) then 
            remove_duplicates locs ss
          else 
            (loc, s) :: (remove_duplicates (loc :: locs) ss))
    in
    (* let substitution : IT.t Subst.t = {replace = [(Sym.fresh_pretty "return", IT.(IT (Sym (Sym.fresh_pretty "__cn_ret"), BT.Unit)))]; relevant = SymSet.empty} in *)
    (* let post_with_ret = RT.subst substitution post in *)
    let (return_cn_binding, return_cn_decl) = match rm_ctype c_return_type with 
      | C.Void -> ([], [])
      | _ ->
        let return_cn_sym = Sym.fresh_pretty "return_cn" in
        let sct_opt = Sctypes.of_ctype c_return_type in 
        let sct = match sct_opt with 
          | Some t -> t
          | None -> failwith "No sctype conversion"
        in
        let bt = BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct in 
        let real_return_ctype = bt_to_ail_ctype bt in 
        let return_cn_binding = create_binding return_cn_sym real_return_ctype in 
        let cn_ret_ail_expr_ = A.(AilEident (Sym.fresh_pretty "__cn_ret")) in
        let return_cn_decl = A.(AilSdeclaration [(return_cn_sym, Some (mk_expr (add_conversion_fn cn_ret_ail_expr_ bt)))]) in
        ([return_cn_binding], [mk_stmt return_cn_decl])
    in
    let stats = remove_duplicates [] stats in
    let ail_statements = List.map (fun stat_pair -> cn_to_ail_statements dts globals stat_pair) stats in 
    let (post_bs, post_ss, ownership_ctypes') = cn_to_ail_post_internal dts globals ownership_ctypes preds post in 
    let block = A.(AilSblock (return_cn_binding @ post_bs, return_cn_decl @ post_ss)) in
    {pre = ([], []); post = ([], [block]); in_stmt = ail_statements; ownership_ctypes = ownership_ctypes'}


let rec cn_to_ail_pre_post_aux_internal dts preds globals c_return_type = function 
  | AT.Computational ((sym, bt), info, at) -> 
    let cn_sym = generate_sym_with_suffix ~suffix:"_cn" sym in 
    let cn_ctype = bt_to_ail_ctype bt in 
    let binding = create_binding cn_sym cn_ctype in 
    let rhs = add_conversion_fn A.(AilEident sym) bt in 
    let decl = A.(AilSdeclaration [(cn_sym, Some (mk_expr rhs))]) in
    let subst_at = Core_to_mucore.fn_spec_instrumentation_sym_subst_at (sym, bt, cn_sym) at in
    let ail_executable_spec = cn_to_ail_pre_post_aux_internal dts preds globals c_return_type subst_at in 
    prepend_to_precondition ail_executable_spec ([binding], [decl])
  | AT.L lat -> 
    cn_to_ail_lat_internal_2 dts globals [] preds c_return_type lat
  
let cn_to_ail_pre_post_internal dts preds globals c_return_type = function 
  | Some internal -> cn_to_ail_pre_post_aux_internal dts preds globals c_return_type internal
  | None -> empty_ail_executable_spec
