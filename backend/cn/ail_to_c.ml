[@@@warning "-27"]
module CF=Cerb_frontend
open Executable_spec_utils
module A=CF.AilSyntax
module C=CF.Ctype

let ident_list = [
  ("return", "__cn_ret");
  ("power", "pow")
]

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

let pp_ail_post_helper ident_name arg_names_opt =
  let suffix = 
    match arg_names_opt with
    | Some arg_names -> 
      let is_ident_function_arg = (List.mem String.equal ident_name arg_names) in
      if is_ident_function_arg then "_old" else ""
    | None -> ""
  in
  ident_name ^ suffix


let rec pp_ail_expr ?(arg_names_opt=None) ail_expr =
  match ail_expr with
    | A.(AilEident sym) -> 
      let sym_str = CF.String_ail.string_of_cn_id sym in
      let str_from_list_opt = List.assoc_opt String.equal sym_str ident_list in
      let ident_str =
      (match str_from_list_opt with
        | Some str -> str
        | None -> sym_str)
      in 
      let ident_str = pp_ail_post_helper ident_str arg_names_opt in 
      ident_str
    | A.(AilEconst ail_const) -> pp_ail_const ail_const
    | A.(AilEbinary (x, bop, y)) -> (pp_ail_expr ~arg_names_opt (rm_expr x)) ^ " " ^ (pp_ail_binop bop) ^ " " ^ (pp_ail_expr ~arg_names_opt (rm_expr y))
    | A.(AilEunary (Bnot, ail_expr)) -> "!(" ^ (pp_ail_expr ~arg_names_opt (rm_expr ail_expr)) ^ ")"
    | A.(AilEcond (e1, Some e2, e3)) -> (pp_ail_expr ~arg_names_opt (rm_expr e1)) ^ " ? " ^ (pp_ail_expr ~arg_names_opt (rm_expr e2)) ^ " : " ^ (pp_ail_expr ~arg_names_opt (rm_expr e3)) 
    | A.(AilEsizeof (_, ct)) -> "sizeof(" ^ pp_ctype ct ^ ")"
    | A.(AilEcast (_, ctype , expr)) -> "(" ^ pp_ctype ctype ^ ") " ^ pp_ail_expr ~arg_names_opt (rm_expr expr)
    | A.(AilEcall (AnnotatedExpression (_, _, _, f), ail_exprs)) -> 
      let str_exprs = List.map (fun e -> pp_ail_expr ~arg_names_opt (rm_expr e)) ail_exprs in
      pp_ail_expr ~arg_names_opt f ^ "(" ^ String.concat ", " str_exprs ^ ")" 
    | A.AilEassert ail_expr -> 
        "assert(" ^ pp_ail_expr ~arg_names_opt (rm_expr ail_expr) ^ ")"
    | _ -> 
      Printf.printf "entered this case\n";
      pp_ail_default ail_expr

let pp_ail_stmt_default ail_stmt = CF.String_ail.string_of_statement (mk_stmt ail_stmt)


  
let pp_ail_stmt ((ail_stmt, extra) as ail_info) arg_names_opt = 
  match ail_info with
  | (A.AilSdeclaration ((name, Some decl) :: _), ct) -> 
    (* TODO: Hack! Remove. *)
    let type_str = (match ct with 
      | Some ctype -> pp_ctype ctype ^ " "
      | None -> "const int ")
    in
    let name_var = A.(AilEident name) in
    type_str ^ pp_ail_expr name_var ^ " = " ^ pp_ail_expr ~arg_names_opt (rm_expr decl)
  | (A.(AilSexpr ail_expr), _) -> pp_ail_expr ~arg_names_opt (rm_expr ail_expr)
  | _ -> pp_ail_stmt_default ail_stmt

