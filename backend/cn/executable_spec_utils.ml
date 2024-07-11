module CF=Cerb_frontend
module A=CF.AilSyntax
module C=CF.Ctype
module Cn=CF.Cn


let empty_qualifiers : C.qualifiers = {const = false; restrict = false; volatile = false}
let const_qualifiers : C.qualifiers = {const = true; restrict = false; volatile = false}

let empty_attributes = CF.Annot.Attrs []

let mk_ctype ?(annots=[]) ctype_ = C.Ctype (annots, ctype_)


let rm_ctype (C.Ctype (_, ctype_)) = ctype_

let get_typedef_string_aux (C.Ctype (annots, _)) = match annots with
  | CF.Annot.Atypedef sym :: _ -> Some (Sym.pp_string sym)
  | _ -> None

let get_typedef_string (C.(Ctype (_, ctype_))) =
  match ctype_ with
    | Pointer (_, ctype) -> get_typedef_string_aux ctype
    | _ -> None


let mk_expr expr_ =
  A.AnnotatedExpression (
    CF.GenTypes.GenLValueType (empty_qualifiers, mk_ctype C.Void, false),
     [], Cerb_location.unknown, expr_)

let get_expr_strs = function
  | (A.AnnotatedExpression (CF.GenTypes.GenLValueType (_, _, _), strs, _, _)) -> strs
  | _ -> []

let mk_cn_expr cn_expr_ =
  Cn.CNExpr (Cerb_location.unknown, cn_expr_)

let rm_cn_expr (Cn.CNExpr (_, cn_expr_))
  = cn_expr_


let mk_stmt stmt_ =
  A.AnnotatedStatement (Cerb_location.unknown, CF.Annot.Attrs [], stmt_)

let rm_expr (A.AnnotatedExpression (_, _, _, expr_)) = expr_

let rm_stmt (A.AnnotatedStatement (_, _, stmt_)) = stmt_

let empty_ail_str = "empty_ail"
let empty_ail_expr = A.(AilEident (Sym.fresh_pretty empty_ail_str))
let empty_ail_stmt = A.(AilSexpr (mk_expr empty_ail_expr))

let is_empty_ail_stmt = function
  | A.(AilSexpr (AnnotatedExpression (_, _, _, AilEident sym))) -> String.equal empty_ail_str (Sym.pp_string sym)
  | _ -> false






let rec list_split_three = function
  | [] -> ([], [], [])
  | (x, y, z) :: rest ->
    let (xs, ys, zs) = list_split_three rest in
    (x::xs, y::ys, z::zs)


type cn_dependencies = CF.Symbol.sym list

type cn_dependency_graph = {
  cn_functions_with_dependencies : ( ((CF.Symbol.sym, C.ctype) Cn.cn_function)) list;
}

let compute_cn_dependencies ail_prog =
  ail_prog

let ifndef_wrap ifndef_str str =
  "#ifndef " ^ ifndef_str ^ "\n#define " ^ ifndef_str ^ "\n" ^ str ^ "\n#endif"  
  

let generate_include_header (file_name, is_system_header) =
  let pre = "#include " in
  let incl =
    if is_system_header then
      "<" ^ file_name ^ ">"
    else
      "\"" ^ file_name ^ "\""
  in
  pre ^ incl ^ "\n" 

let get_ctype_without_ptr ctype = match rm_ctype ctype with
  | C.(Pointer (_, ct)) -> ct
  | _ -> ctype

let is_pointer ctype = match rm_ctype ctype with 
  | C.(Pointer _) -> true
  | _ -> false

let rec _transform_ctype_for_ptr (C.(Ctype (annots, ctype)) as original_ctype) = 
  let mk_pointer_from_ctype ctype' = C.(Ctype (annots, Pointer (empty_qualifiers, ctype'))) in 
  match ctype with 
  | Array (ctype', _) 
  | Pointer (_, ctype') -> mk_pointer_from_ctype (_transform_ctype_for_ptr ctype') 
  | _ -> original_ctype


let rec str_of_ctype ctype = match rm_ctype ctype with 
    | C.(Pointer (_, ctype')) ->
      str_of_ctype ctype' ^ " pointer"
    | C.(Array (ctype, num_elements_opt)) -> (match num_elements_opt with 
      | Some num_elements -> 
        str_of_ctype ctype ^ " " ^ string_of_int (Z.to_int num_elements)
      | None -> str_of_ctype (mk_ctype C.(Pointer (empty_qualifiers, ctype))))
    | _ -> 
      let doc = CF.Pp_ail.pp_ctype ~executable_spec:true empty_qualifiers ctype in
      CF.Pp_utils.to_plain_pretty_string doc
  

let rec execCtypeEqual (C.Ctype (_, ty1)) (C.Ctype (_, ty2)) =
  let paramsEqual ((qs1, ty1, b1), (qs2, ty2, b2)) =
    (C.qualifiersEqual qs1 qs2 && execCtypeEqual ty1 ty2 && b1 == b2) 
  in
  match (ty1, ty2) with
    | (Void, Void) -> true
    | (Basic bty1, Basic bty2) ->
        C.basicTypeEqual bty1 bty2
    | (Array (ty1, n1_opt), Array (ty2, n2_opt)) ->
      execCtypeEqual ty1 ty2 && n1_opt == n2_opt
    | (Function ((qs1, ty1), params1, b1),
        Function ((qs2, ty2), params2, b2)) ->
        let bools = List.map paramsEqual (List.combine params1 params2) in 
        C.qualifiersEqual qs1 qs2 && execCtypeEqual ty1 ty2 &&
        List.fold_left (&&) true bools && b1 == b2
    | (FunctionNoParams (qs1, ty1),
        FunctionNoParams (qs2, ty2)) ->
        C.qualifiersEqual qs1 qs2 && execCtypeEqual ty1 ty2
    | (Pointer (qs1, ty1), Pointer (qs2, ty2)) ->
        C.qualifiersEqual qs1 qs2 && execCtypeEqual ty1 ty2
    | (Atomic ty1, Atomic ty2) ->
        execCtypeEqual ty1 ty2
    | (Struct id1, Struct id2) ->
        id1 == id2
    | (Union id1, Union id2) ->
        id1 == id2
    | _ ->
        false



let str_of_it_ = function
  | Terms.Sym sym -> Sym.pp_string sym
  | _ -> ""

let create_binding sym ctype = 
    A.(sym, ((Cerb_location.unknown, Automatic, false), None, empty_qualifiers, ctype))

let find_ctype_from_bindings bindings sym = 
  let (_, (_, _, _, ctype)) = List.find (fun (sym', _) -> Sym.equal sym sym') bindings in 
  ctype

(* Decl_object  of (storageDuration * bool) * maybe alignment * qualifiers * ctype*)
let create_decl_object ctype = 
  A.(Decl_object ((Automatic, false), None, empty_qualifiers, ctype))

(*  declarations: list (ail_identifier * (Loc.t * Annot.attributes * declaration)) *)
let create_declaration sym decl = 
  (sym, (Cerb_location.unknown, CF.Annot.Attrs [], decl))