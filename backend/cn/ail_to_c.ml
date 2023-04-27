[@@@warning "-27"]
module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let pp_ail_default ail_expr = CF.String_ail.string_of_expression ~executable_spec:true (mk_expr ail_expr)

let pp_ail_const ail_const = 
  match ail_const with
    | A.ConstantInteger (IConstant (n, _, Some B)) -> Bool.to_string ((Z.to_int n) == 1)
    | A.ConstantIndeterminate _ -> "()" (* TODO: Check *)
    | _ -> pp_ail_default A.(AilEconst ail_const)

let pp_ail_arithmetic_binop = function
    | A.Add -> "+"
    | A.Sub -> "-"
    | A.Mul -> "*"
    | A.Div -> "/"
    | _ -> ""

let pp_ail_binop = function
  | A.(Arithmetic arithOp) -> pp_ail_arithmetic_binop arithOp
  | A.Eq -> "=="
  | A.Ne -> "!="
  | A.Lt -> "<"
  | A.Gt -> ">"
  | A.Le -> "<="
  | A.Ge -> ">="
  | A.Or -> "||"
  | A.And -> "&&"
  | _ -> ""



let pp_ctype ctype = CF.Pp_utils.to_plain_string (CF.Pp_ail.pp_ctype empty_qualifiers ctype)

let rec pp_ail_expr ail_expr =
  match ail_expr with
    | A.(AilEident sym) -> 
      let sym_str = CF.String_ail.string_of_cn_id sym in
      if String.equal sym_str "return" then
        "__cn_ret"
      else
        sym_str
    | A.(AilEconst ail_const) -> pp_ail_const ail_const
    | A.(AilEbinary (x, bop, y)) -> (pp_ail_expr (rm_expr x)) ^ " " ^ (pp_ail_binop bop) ^ " " ^ (pp_ail_expr (rm_expr y))
    | A.(AilEunary (Bnot, ail_expr)) -> "!(" ^ (pp_ail_expr (rm_expr ail_expr)) ^ ")"
    | A.(AilEcond (e1, Some e2, e3)) -> (pp_ail_expr (rm_expr e1)) ^ " ? " ^ (pp_ail_expr (rm_expr e2)) ^ " : " ^ (pp_ail_expr (rm_expr e3)) 
    | A.(AilEsizeof (_, ct)) -> "sizeof(" ^ pp_ctype ct ^ ")"
    | A.(AilEcast (_, ctype , expr)) -> "(" ^ pp_ctype ctype ^ ") " ^ pp_ail_expr (rm_expr expr)
    | A.(AilEcall (AnnotatedExpression (_, _, _, f), ail_exprs)) -> 
      let str_exprs = List.map (fun e -> pp_ail_expr (rm_expr e)) ail_exprs in
      pp_ail_expr f ^ "(" ^ String.concat ", " str_exprs ^ ")" 
    | A.AilEassert ail_expr -> 
        "assert(" ^ pp_ail_expr (rm_expr ail_expr) ^ ")"
    | _ -> pp_ail_default ail_expr

let pp_ail_stmt_default ail_stmt = CF.String_ail.string_of_statement (mk_stmt ail_stmt)

let pp_ail_stmt ((ail_stmt, extra) as ail_info) = match ail_info with
  | (A.AilSdeclaration ((name, Some decl) :: _), Some ctype) -> (* TODO: Add type *)
    let name_var = A.(AilEident name) in
    pp_ctype ctype ^ " " ^ pp_ail_expr name_var ^ " = " ^ pp_ail_expr (rm_expr decl)
  | (A.(AilSexpr ail_expr), _) -> pp_ail_expr (rm_expr ail_expr)
  | _ -> pp_ail_stmt_default ail_stmt
(* frontend/model/symbol.lem - fresh_pretty function for generating Sym with unimportant digest and nat *)