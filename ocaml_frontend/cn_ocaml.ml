open Cn

open Pp_prelude
open Pp_ast
open Pp_symbol

open Location_ocaml


module P = PPrint


let string_of_error = function
  | CNErr_lowercase_predicate (Symbol.Identifier (_, str)) ->
      "predicate name `" ^ str ^ "' does not start with an uppercase"
  | CNErr_predicate_redeclaration ->
      "redeclaration of predicate name"
  | CNErr_unknown_predicate ->
      "undeclared predicate name"
  | CNErr_invalid_tag ->
      "tag name is no declared or a union tag"
  | CNErr_unknown_identifier (CN_oarg, Symbol.Identifier (_, str)) ->
      "the oarg `" ^ str ^ "' is not declared"
  | CNErr_unknown_identifier (CN_logical, Symbol.Identifier (_, str)) ->
        "the logical variable `" ^ str ^ "' is not declared"
  | CNErr_unknown_identifier (CN_predicate, Symbol.Identifier (_, str)) ->
        "the predicate `" ^ str ^ "' is not declared"
  | CNErr_unknown_identifier (CN_resource, Symbol.Identifier (_, str)) ->
        "the resource variable `" ^ str ^ "' is not declared"
  | CNErr_missing_oarg sym ->
      "missing an assignment for the oarg `" ^ Pp_symbol.to_string_pretty sym ^ "'" 
    


module type PP_CN = sig
  type ident
  type ty
  val pp_ident: ident -> P.document
  val pp_ty: ty -> P.document
end

module MakePp (Conf: PP_CN) = struct
  let rec pp_base_type = function
    | CN_unit ->
        pp_type_keyword "unit"
    | CN_bool ->
        pp_type_keyword "bool"
    | CN_integer ->
        pp_type_keyword "integer"
    | CN_real ->
        pp_type_keyword "real"
    | CN_loc ->
        pp_type_keyword "loc"
    | CN_struct ident ->
        pp_type_keyword "struct" ^^^ P.squotes (Conf.pp_ident ident)
    | CN_map (bTy1, bTy2) ->
        pp_type_keyword "map" ^^ P.angles (pp_base_type bTy1 ^^ P.comma ^^^ pp_base_type bTy2)
    | CN_list bTy ->
        pp_type_keyword "list" ^^ P.angles (pp_base_type bTy)
    | CN_tuple bTys ->
        pp_type_keyword "tuple" ^^ P.angles (comma_list pp_base_type bTys)
    | CN_set bTy ->
        pp_type_keyword "set" ^^ P.angles (pp_base_type bTy)

  let pp_cn_binop = function
    | CN_add -> P.plus
    | CN_sub -> P.minus
    | CN_mul -> P.star
    | CN_div -> P.slash
    | CN_equal -> P.equals ^^ P.equals
    | CN_inequal -> P.backslash ^^ P.equals
    | CN_lt -> P.langle
    | CN_gt -> P.rangle
    | CN_le -> P.langle ^^ P.equals
    | CN_ge -> P.rangle ^^ P.equals
    | CN_or -> P.bar ^^ P.bar
    | CN_and -> P.ampersand ^^ P.ampersand
  
  let rec dtree_of_cn_expr = function
    | CNExpr_NULL ->
        Dleaf (pp_ctor "CNExpr_NULL")
    | CNExpr_var ident ->
        Dleaf (pp_ctor "CNExpr_var" ^^^ P.squotes (Conf.pp_ident ident))
    | CNExpr_memberof (ident, ident_membr) ->
        Dleaf (pp_ctor "CNExpr_member" ^^^
               P.squotes (Conf.pp_ident ident) ^^ P.dot ^^^ P.squotes (pp_identifier ident_membr))
    | CNExpr_binop (bop, e1, e2) ->
        Dnode (pp_ctor "CNExpr_add" ^^^ pp_cn_binop bop, [dtree_of_cn_expr e1; dtree_of_cn_expr e2])

  let dtree_of_cn_pred = function
    | CN_owned ty ->
      Dleaf (pp_stmt_ctor "CN_owned" ^^^ Conf.pp_ty ty)
    | CN_block ty ->
      Dleaf (pp_stmt_ctor "CN_block" ^^^ Conf.pp_ty ty)
    | CN_named ident ->
        Dleaf (pp_stmt_ctor "CN_named" ^^^ P.squotes (Conf.pp_ident ident))

  let dtree_of_cn_resource = function
    | CN_pred (pred, es) ->
        Dnode (pp_stmt_ctor "CN_pred", dtree_of_cn_pred pred :: List.map dtree_of_cn_expr es)
    | CN_each (ident, bTy, e, pred, es) ->
        Dnode ( pp_stmt_ctor "CN_each" ^^^ P.squotes (Conf.pp_ident ident) ^^^ P.colon ^^^ pp_base_type bTy
              , List.map dtree_of_cn_expr es )
  
  let rec dtree_of_cn_clause = function
    | CN_letResource (ident, res, c) ->
        Dnode ( pp_stmt_ctor "CN_letResource" ^^^ P.squotes (Conf.pp_ident ident)
              , [dtree_of_cn_resource res; dtree_of_cn_clause c])
    | CN_letExpr (ident, e, c) ->
        Dnode ( pp_stmt_ctor "CN_letExpr" ^^^ P.squotes (Conf.pp_ident ident)
              , [dtree_of_cn_expr e; dtree_of_cn_clause c])
    | CN_assert (e, c) ->
        Dnode (pp_stmt_ctor "CN_assert", [dtree_of_cn_expr e; dtree_of_cn_clause c])
    | CN_return (_, xs) ->
        let docs =
            List.map (fun (ident, e) ->
              Dnode (Conf.pp_ident ident, [dtree_of_cn_expr e])
            ) xs in
        Dnode (pp_stmt_ctor "CN_return", docs)

  let rec dtree_of_cn_clauses = function
    | CN_clause c ->
        dtree_of_cn_clause c
    | CN_if (e, c1, c2) ->
        Dnode (pp_stmt_ctor "CN_if", [dtree_of_cn_expr e; dtree_of_cn_clause c1; dtree_of_cn_clauses c2])


  let dtree_of_cn_predicate pred =
    let dtrees_of_args xs =
      List.map (fun (bTy, ident) ->
        Dleaf (Conf.pp_ident ident ^^ P.colon ^^^ pp_base_type bTy)
      ) xs in
    Dnode ( pp_ctor "[CN]predicate" ^^^ P.squotes (Conf.pp_ident pred.cn_pred_name)
          , [ Dnode (pp_ctor "[CN]iargs", dtrees_of_args pred.cn_pred_iargs)
            ; Dnode (pp_ctor "[CN]oargs", dtrees_of_args pred.cn_pred_oargs)
            ; Dnode (pp_ctor "[CN]clauses", [dtree_of_cn_clauses pred.cn_pred_clauses]) ] ) 
end

module PpCabs = MakePp (struct
  type ident = Symbol.identifier
  type ty = Cabs.type_name
  let pp_ident = pp_identifier
  let pp_ty _ = failwith "PpCabs.pp_type_name"
end)

module PpAil = MakePp (struct
  type ident = Symbol.sym
  type ty = Ctype.ctype
  let pp_ident sym = !^ (Colour.ansi_format [Yellow] (Pp_symbol.to_string_pretty sym))
  let pp_ty ty = Pp_ail.pp_ctype Ctype.no_qualifiers ty
end)