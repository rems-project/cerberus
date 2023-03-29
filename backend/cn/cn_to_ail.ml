module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
open CF.Cn
module A=CF.AilSyntax

let mk_expr expr_ = 
  A.AnnotatedExpression ((), [], Cerb_location.unknown, expr_)


let cn_to_ail_const = function
| CNConst_integer n -> mk_expr (A.(AilEconst (ConstantInteger (IConstant (n, Decimal, None)))))
| _ -> failwith "TODO"

(* frontend/model/ail/ail_syntax.ml *)
let cn_to_ail_expr (CNExpr (loc, expr_)) =
  match expr_ with
    | CNExpr_const cn_cst -> cn_to_ail_const cn_cst
    | CNExpr_value_of_c_atom (sym, _) -> 
      Printf.printf ">> \x1b[31m%s\x1b0m]\n" (CF.Pp_symbol.to_string_pretty sym);
      mk_expr (A.(AilEident sym))
    | _ -> failwith "TODO"




let pp_ail = CF.String_ail.string_of_expression

(* frontend/model/symbol.lem - fresh_pretty function for generating Sym with unimportant digest and nat *)