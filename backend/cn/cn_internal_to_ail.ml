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

(* TODO: Change to use internal  *)

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
  | CN_is_shape -> failwith "TODO"
  


let cn_to_ail_const = function
  | CNConst_NULL -> A.(AilEconst ConstantNull)
  | CNConst_integer n -> A.(AilEconst (ConstantInteger (IConstant (n, Decimal, None))))
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
let rec cn_to_ail_expr_aux_internal 
: type a. _ option -> (_ Cn.cn_datatype) list -> IT.t -> a dest -> a
= fun const_prop dts (IT (term_, basetype)) d ->
  let cn_to_ail_expr_aux_internal_at_env : type a. _ cn_expr -> string -> a dest -> a
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
  in
  match term_ with
  | Const const -> failwith "TODO"
  | Sym sym -> failwith "TODO"
  | Binop (op, t1, t2) -> failwith "TODO"
  | Not t -> failwith "TODO"
  | ITE (t1, t2, t3) -> failwith "TODO"
  | EachI ((r_start, (sym, bt), r_end), t) -> failwith "TODO"
  (* add Z3's Distinct for separation facts  *)
  | Tuple ts -> failwith "TODO"
  | NthTuple (i, t) -> failwith "TODO"
  | Struct (tag, ms) -> failwith "TODO"
  | StructMember (t, m) -> failwith "TODO"
  | StructUpdate ((t1, m), t2) -> failwith "TODO"
  | Record ms -> failwith "TODO"
  | RecordMember (t, m) -> failwith "TODO"
  | RecordUpdate ((t1, m), t2) -> failwith "TODO"
  (* | DatatypeCons of Sym.t * 'bt term TODO: will be removed *)
  (* | DatatypeMember of 'bt term * Id.t TODO: will be removed *)
  (* | DatatypeIsCons of Sym.t * 'bt term TODO: will be removed *)
  | Constructor (nm, ms) -> failwith "TODO"
  | MemberOffset (tag, m) -> failwith "TODO"
  | ArrayOffset (ct, index) -> failwith "TODO"
  | Nil -> failwith "TODO"
  | Cons (x, xs) -> failwith "TODO"
  | List ts -> failwith "TODO"
  | Head xs -> failwith "TODO"
  | Tail xs -> failwith "TODO"
  | NthList (t1, t2, t3) -> failwith "TODO"
  | ArrayToList (t1, t2, t3) -> failwith "TODO"
  | Representable (ct, t) -> failwith "TODO"
  | Good (ct, t) -> failwith "TODO"
  | Aligned t_and_align -> failwith "TODO"
  | WrapI (ct, t) -> failwith "TODO"
  | MapConst (bt, t) -> failwith "TODO"
  | MapSet (t1, t2, t3) -> failwith "TODO"
  | MapGet (t1, t2) -> failwith "TODO"
  | MapDef ((sym, bt), t) -> failwith "TODO"
  | Apply (sym, ts) -> failwith "TODO"
  | Let ((var, t1), t2) -> failwith "TODO"
  | Match (t, ps) -> failwith "TODO"
  | Cast (bt, t) -> failwith "TODO"
  | _ -> failwith "TODO"

let cn_to_ail_expr_internal
  : type a. (_ Cn.cn_datatype) list -> _ cn_expr -> a dest -> a
  = fun dts cn_expr d ->
    cn_to_ail_expr_aux_internal None dts cn_expr d


type 'a ail_datatype = {
  structs: (C.union_tag * (CF.Annot.attributes * C.tag_definition)) list;
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
  let enum = (enum_sym, (attrs, enum_tag_definition)) in
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
    (lc_constructor, (empty_attributes, generate_tag_definition members))
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
  {structs = enum :: structs; decls = []; stats = []}



(* TODO: Finish with rest of function - maybe header file with A.Decl_function (cn.h?) *)
let cn_to_ail_function cn_function cn_datatypes = 
  let ail_func_body =
  match cn_function.cn_func_body with
    | Some e ->
      let ss = cn_to_ail_expr_internal cn_datatypes e Return in
      List.map mk_stmt ss
    | None -> []
  in
  (* let var_decls = List.map (fun (sym, decl) -> (sym, (Cerb_location.unknown, empty_attributes, decl))) var_decls in *)
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
      let ss = cn_to_ail_expr_internal cn_datatypes e_ Assert in 
      List.map mk_stmt ss
  | CN_assert_qexp (ident, bTy, e1, e2) -> failwith "TODO"


let cn_to_ail_condition cn_condition type_map cn_datatypes = 
  match cn_condition with
  | CN_cletResource (loc, name, resource) -> ([A.AilSskip], None) (* TODO *)
  | CN_cletExpr (_, name, expr) -> 
    (* TODO: return declarations too *)
    let ss = cn_to_ail_expr_internal cn_datatypes expr (AssignVar name) in
    let sfb_type = SymTable.find type_map name in
    let basetype = SurfaceBaseTypes.to_basetype sfb_type in
    let cn_basetype = bt_to_cn_base_type basetype in
    let ctype = cn_to_ail_base_type cn_basetype in
    (ss, Some (mk_ctype ctype))
  | CN_cconstr (loc, constr) -> 
    let ail_constr = cn_to_ail_assertion constr cn_datatypes in
    let ail_stats_ = List.map rm_stmt ail_constr in
    (ail_stats_, None)
