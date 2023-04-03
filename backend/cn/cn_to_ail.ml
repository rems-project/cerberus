module CF=Cerb_frontend
(* module CB=Cerb_backend
open CB.Pipeline
open Setup *)
open CF.Cn
module A=CF.AilSyntax
module C=CF.Ctype

let rm_expr (A.AnnotatedExpression (_, _, _, expr_)) = expr_

let mk_expr expr_ = 
  A.AnnotatedExpression ((), [], Cerb_location.unknown, expr_)

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
  


let cn_to_ail_const = function
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
  (* Representing bool as integer with integerSuffix B *)
  | CNConst_bool b -> A.(AilEconst (ConstantInteger (IConstant (Z.of_int (Bool.to_int b), Decimal, Some B))))
  | CNConst_unit -> A.(AilEconst (ConstantIndeterminate C.(Ctype ([], Void))))
 

(* frontend/model/ail/ailSyntax.lem *)
(* ocaml_frontend/generated/ailSyntax.ml *)
let rec cn_to_ail_expr (CNExpr (loc, expr_)) =
  match expr_ with
    | CNExpr_const cn_cst -> cn_to_ail_const cn_cst
    | CNExpr_value_of_c_atom (sym, _) -> A.(AilEident sym)
    | CNExpr_var sym -> A.(AilEident sym) (* TODO: Check. Need to do more work if this is only a CN var *)
    | CNExpr_deref e -> A.(AilEunary (Indirection, mk_expr (cn_to_ail_expr e)))
    (* 
    | CNExpr_var sym -> parens (typ (!^ "var") (Sym.pp sym))
    | CNExpr_deref e -> !^ "(deref ...)"
    | CNExpr_list es_ -> !^ "[...]"
    | CNExpr_memberof (e, xs) -> !^ "_." ^^ Id.pp xs
    | CNExpr_memberupdates (e, _updates) -> !^ "{_ with ...}"
    | CNExpr_arrayindexupdates (e, _updates) -> !^ "_ [ _ = _ ...]"
    *)
    | CNExpr_binop (bop, x, y) -> A.AilEbinary (mk_expr (cn_to_ail_expr x), cn_to_ail_binop bop, mk_expr (cn_to_ail_expr y))
    (*
    | CNExpr_sizeof ct -> !^ "(sizeof _)"
    | CNExpr_offsetof (tag, member) -> !^ "(offsetof (_, _))"
    | CNExpr_membershift (e, member) -> !^ "&(_ -> _)"
    | CNExpr_cast (bt, expr) -> !^ "(cast (_, _))"
    | CNExpr_call (sym, exprs) -> !^ "(" ^^ Sym.pp sym ^^^ !^ "(...))"
    | CNExpr_cons (c_nm, exprs) -> !^ "(" ^^ Sym.pp c_nm ^^^ !^ "{...})"
    | CNExpr_each (sym, r, e) -> !^ "(each ...)"
    | CNExpr_ite (e1, e2, e3) -> !^ "(if ... then ...)"
    | CNExpr_good (ty, e) -> !^ "(good (_, _))"
    | CNExpr_unchanged e -> !^"(unchanged (_))"
    | CNExpr_at_env (e, es) -> !^"{_}@_"
    | CNExpr_not e -> !^"!_" 
    *)
    | _ -> failwith "TODO"



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

let rec pp_ail ail_expr =
  match ail_expr with
    | A.(AilEconst ail_const) -> pp_ail_const ail_const
    | A.(AilEbinary (x, bop, y)) -> (pp_ail (rm_expr x)) ^ (pp_ail_binop bop) ^ (pp_ail (rm_expr y))
    | _ -> pp_ail_default ail_expr


(* frontend/model/symbol.lem - fresh_pretty function for generating Sym with unimportant digest and nat *)