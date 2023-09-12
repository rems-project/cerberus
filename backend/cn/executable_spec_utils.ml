module CF=Cerb_frontend
module A=CF.AilSyntax
module C=CF.Ctype
module Cn=CF.Cn


let empty_qualifiers : C.qualifiers = {const = false; restrict = false; volatile = false}
let const_qualifiers : C.qualifiers = {const = true; restrict = false; volatile = false}

let empty_attributes = CF.Annot.Attrs []

let mk_ctype ?(annots=[]) ctype_ = C.Ctype (annots, ctype_)

let rm_ctype (C.Ctype (_, ctype_)) = ctype_

let mk_expr ?(strs=[]) expr_ = 
  A.AnnotatedExpression (
    CF.GenTypes.GenLValueType (empty_qualifiers, mk_ctype C.Void, false),
     strs, Cerb_location.unknown, expr_)

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

