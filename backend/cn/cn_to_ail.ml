[@@@warning "-27"]
module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
open CF.Cn
module A=CF.AilSyntax
module C=CF.Ctype

let mk_expr expr_ = 
  A.AnnotatedExpression ((), [], Cerb_location.unknown, expr_)


let cn_to_ail_const cn_const =
let ail_const = match cn_const with
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
  | CNConst_bool b -> A.(AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int b), Decimal, Some B))))
  (* | CNConst_unit -> (A.(AilEconst (ConstantInteger (IConstant (Z.of_int 0, Decimal, None)))), Some "unit") *)
  | CNConst_unit -> A.(AilEconst (ConstantIndeterminate C.(Ctype ([], Void))))
in 
ail_const

(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
let cn_to_ail_expr (CNExpr (loc, expr_)) =
  match expr_ with
    | CNExpr_const cn_cst -> cn_to_ail_const cn_cst
    | CNExpr_value_of_c_atom (sym, _) -> A.(AilEident sym)
    | _ -> failwith "TODO"



let pp_ail_default ail_expr = CF.String_ail.string_of_expression (mk_expr ail_expr)

let pp_ail_special_const ail_const = 
  match ail_const with
    | A.ConstantInteger (IConstant (n, _, Some B)) -> Bool.to_string ((Z.to_int n) == 1)
    | A.ConstantIndeterminate _ -> "()" (* TODO: Check *)
    | _ -> pp_ail_default A.(AilEconst ail_const)

let pp_ail ail_expr =
  match ail_expr with
    | A.(AilEconst ail_const) -> pp_ail_special_const ail_const
    | _ -> pp_ail_default ail_expr


(* frontend/model/symbol.lem - fresh_pretty function for generating Sym with unimportant digest and nat *)