module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let pp_ail_default ail_expr = CF.String_ail.string_of_expression (mk_expr ail_expr)

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

let rec pp_ail ail_expr =
  match ail_expr with
    | A.(AilEident sym) -> CF.String_ail.string_of_cn_id sym
    | A.(AilEconst ail_const) -> pp_ail_const ail_const
    | A.(AilEbinary (x, bop, y)) -> (pp_ail (rm_expr x)) ^ (pp_ail_binop bop) ^ (pp_ail (rm_expr y))
    | A.(AilEunary (Bnot, ail_expr)) -> "!(" ^ (pp_ail (rm_expr ail_expr)) ^ ")"
    | A.(AilEcond (e1, Some e2, e3)) -> (pp_ail (rm_expr e1)) ^ " ? " ^ (pp_ail (rm_expr e2)) ^ " : " ^ (pp_ail (rm_expr e3)) 
    | A.(AilEcond (_, None, _)) -> pp_ail_default ail_expr
    | A.(AilEsizeof (_, ct)) -> "sizeof(" ^ pp_ctype ct ^ ")"
    | A.(AilEcast (_, ctype , expr)) -> "(" ^ pp_ctype ctype ^ ") " ^ pp_ail (rm_expr expr)
    | A.(AilEcall (A.AnnotatedExpression (_, _, _, f), ail_exprs)) -> 
      let str_exprs = List.map (fun e -> pp_ail (rm_expr e)) ail_exprs in
      pp_ail f ^ "(" ^ String.concat ", " str_exprs ^ ")" 
    | _ -> pp_ail_default ail_expr


(* frontend/model/symbol.lem - fresh_pretty function for generating Sym with unimportant digest and nat *)