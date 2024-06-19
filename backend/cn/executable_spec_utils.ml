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



let generate_include_header (file_name, is_system_header) =
  let pre = "#include " in
  let incl =
    if is_system_header then
      "<" ^ file_name ^ ">"
    else
      "\"" ^ file_name ^ "\""
  in
  pre ^ incl ^ "\n"

let str_of_ctype ctype =
  (* Make sure * doesn't get passed back with string *)
  let ctype = match rm_ctype ctype with
    | C.(Pointer (_, ct)) -> ct
    | _ -> ctype
  in
  let doc = CF.Pp_ail.pp_ctype ~executable_spec:true empty_qualifiers ctype in
  CF.Pp_utils.to_plain_pretty_string doc

let str_of_it_ = function
  | Terms.Sym sym -> Sym.pp_string sym
  | _ -> ""

