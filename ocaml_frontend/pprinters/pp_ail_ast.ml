open AilSyntax
open Ctype
open GenTypes

open Cerb_pp_prelude
(*open Pp_ail*)

open Pp_ast
open Cerb_colour

module P = PPrint

open Lem_pervasives
open Either


let pp_symbol sym =
  !^ (ansi_format [Bold; Cyan] (Pp_symbol.to_string_pretty sym))

let pp_qualifiers qs =
  let pp switch str = pp_cond switch (pp_type_keyword str)
  in pp qs.const "const" (
      pp qs.restrict "restrict" (
        pp qs.volatile "volatile" P.empty))



let rec pp_ctype_human_aux qs (Ctype (_, ty)) =
  let prefix_pp_qs =
    if AilTypesAux.is_unqualified qs then
      P.empty
    else
      Pp_ail.pp_qualifiers_human qs ^^ P.space in
  match ty with
    | Void ->
        prefix_pp_qs ^^ !^ "void"
    | Basic bty ->
        prefix_pp_qs ^^ Pp_ail.pp_basicType bty
    | Array (elem_ty, n_opt) ->
        !^ "array" ^^^ P.optional Pp_ail.pp_integer n_opt ^^^ !^ "of" ^^^ pp_ctype_human qs elem_ty
    | Function ((ret_qs, ret_ty), params, is_variadic) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        if not (AilTypesAux.is_unqualified qs) then
          print_endline "TODO: warning, found qualifiers in a function type (this is an UB)"; (* TODO: is it really UB? *)
        
        !^ (if is_variadic then "variadic function" else "function") ^^^
        P.parens (
          comma_list (fun (param_qs, param_ty, isRegister) ->
            (fun z -> if isRegister then !^ "register" ^^^ z else z)
              (pp_ctype_human param_qs param_ty)
          ) params
        ) ^^^
        !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
    | FunctionNoParams ((ret_qs, ret_ty)) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        if not (AilTypesAux.is_unqualified qs) then
          print_endline "TODO: warning, found qualifiers in a function type (this is an UB)"; (* TODO: is it really UB? *)
        
        !^ "function (NO PARAMS)" ^^^
        !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
    | Pointer (ref_qs, ref_ty) ->
        prefix_pp_qs ^^ !^ "pointer to" ^^^ pp_ctype_human ref_qs ref_ty
    | Atomic atom_ty ->
        prefix_pp_qs ^^ !^ "atomic" ^^^ pp_ctype_human no_qualifiers atom_ty
    | Struct tag_sym ->
        prefix_pp_qs ^^ !^ "struct" ^^^ Pp_ail.pp_id ~is_human:true tag_sym
    | Union tag_sym ->
        prefix_pp_qs ^^ !^ "union" ^^^ Pp_ail.pp_id ~is_human:true tag_sym

and pp_ctype_human qs (Ctype (xs, _) as ty) =
  let typedef_opt = List.fold_left (fun acc_opt x ->
    match acc_opt, x with
    | None, Annot.Atypedef sym ->
        Some sym
(*
    | Some attrs1, Annot.Aattrs attrs2 ->
        Some (Annot.combine_attributes attrs1 attrs2)
*)
    | _, _ ->
        acc_opt
  ) None xs in
  match typedef_opt with
    | None ->
        pp_ctype_human_aux qs ty
    | Some sym ->
        pp_ctype_human_aux qs ty ^^^ P.parens (!^ "typedef: " ^^ pp_symbol sym)

let rec pp_genIntegerType_raw = function
 | Concrete ity ->
     !^ "Concrete" ^^ P.brackets (Pp_ail_raw.pp_integerType_raw ity)
 | SizeT ->
     !^ "SizeT"
 | PtrdiffT ->
     !^ "PtrdiffT"
 | PtraddrT ->
     !^ "PtraddrT"
 | Unknown iCst ->
     !^ "Unknown" ^^ P.brackets (Pp_ail.pp_integerConstant iCst)
 | Promote gity ->
     !^ "Promote" ^^ P.brackets (pp_genIntegerType_raw gity)
 | Usual (gity1, gity2) ->
     !^ "Usual" ^^ P.brackets (pp_genIntegerType_raw gity1 ^^ P.comma ^^^ pp_genIntegerType_raw gity2)

let pp_genBasicType_raw = function
 | GenInteger gity ->
     pp_genIntegerType_raw gity
 | GenFloating fty ->
     Pp_ail.pp_floatingType fty

let rec pp_genType = function
 | GenVoid ->
     !^ "void"
 | GenBasic gbty ->
     pp_genBasicType_raw gbty
  | GenArray (ty, None) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_human no_qualifiers ty ^^ P.comma ^^^ !^ "None")
  | GenArray (ty, Some n) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_human no_qualifiers ty ^^ P.comma ^^^ !^ "Some" ^^ P.brackets (Pp_ail.pp_integer n))
 | GenFunction ((ret_qs, ret_ty), params, is_variadic) ->
      !^ "GenFunction" ^^ P.brackets (
        comma_list (fun (qs, ty, isRegister) ->
          P.parens (pp_ctype_human qs ty ^^
                    P.comma ^^^ !^ (if isRegister then "true" else "false"))
        ) params ^^ P.comma ^^ !^ (if is_variadic then "true" else "false")
       ) ^^^
       !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
 | GenFunctionNoParams (ret_qs, ret_ty) ->
      !^ "GenFunctionNoParams" ^^ P.brackets (P.empty) ^^^
       !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
 | GenPointer (ref_qs, ref_ty) ->
     !^ "GenPointer" ^^ P.brackets (pp_ctype_human ref_qs ref_ty)
  | GenStruct sym ->
      !^ "GenStruct" ^^ Pp_ail.pp_id ~is_human:true sym
  | GenUnion sym ->
      !^ "GenUnion" ^^ Pp_ail.pp_id ~is_human:true sym
  | GenAtomic gty ->
      !^ "GenAtomic" ^^ pp_genType gty


let pp_ctype qs ty =
  pp_ctype_human qs ty

(*
  let rec pp_ctype_aux pp_ident_opt qs ty =
    let precOf = function
      | Void
      | Basic _
      | Atomic _
      | Struct _
      | Union _
      | Builtin _ ->
          0
      | Array _ ->
          1
      | Function _ ->
          2
      | Pointer _ ->
          3
    in
    let rec aux p qs ty : P.document -> P.document =
      let p' = precOf ty in
      let aux = aux p' in
      let wrap z = if p' > 0 && p' > p then z else P.parens z in
      begin match ty with
        | Void ->
            fun k -> pp_qualifiers qs ^^ pp_type_keyword "void" ^^ k
        | Basic bty ->
            fun k -> pp_qualifiers qs ^^ pp_basicType bty ^^ k
        | Array (elem_ty, n_opt) ->
            fun k -> aux qs elem_ty k ^^ P.brackets (P.optional pp_integer n_opt)
        | Function (has_proto, (ret_qs, ret_ty), params, is_var) ->
            fun k -> pp_cond has_proto !^"has_prototype"
                (P.squotes (pp_ctype_aux None ret_qs ret_ty
                            ^^ P.parens (comma_list (fun (qs, ty, is_reg) ->
                                pp_cond is_reg (pp_type_keyword "register")
                                  (pp_ctype_aux None qs ty)
                              ) params ^^ pp_cond is_var !^", ..." P.empty)) )
                     ^^ k
        | Pointer (ref_qs, ref_ty) ->
            fun k ->
              aux ref_qs ref_ty (wrap (P.star ^^ pp_qualifiers qs ^^ k))
        | Atomic ty ->
            fun k ->
              pp_qualifiers qs ^^ pp_type_keyword "_Atomic" ^^
              P.parens (aux no_qualifiers ty P.empty) ^^ k
        | Struct sym ->
            fun k ->
              pp_qualifiers qs ^^ pp_type_keyword "struct" ^^^ pp_id_type sym ^^ k
        | Union sym ->
            fun k ->
              pp_qualifiers qs ^^ pp_type_keyword "union" ^^^ pp_id_type sym ^^ k
        | Builtin str ->
            fun k ->
              pp_qualifiers qs ^^ !^ str ^^ k
      end in
    let pp_spaced_ident =
      match pp_ident_opt with Some pp_ident -> P.space ^^ pp_ident | None -> P.empty
    in
    (aux 1 qs ty) pp_spaced_ident
  in
  pp_ctype_aux None qs ty
*)



let rec pp_constant = function
  | ConstantIndeterminate ty ->
      (* NOTE: this is not in C11 *)
      pp_keyword "indet" ^^ P.parens (pp_ctype no_qualifiers ty)
  | ConstantNull ->
      pp_const "NULL"
  | ConstantInteger ic ->
      Pp_ail.pp_integerConstant ic
  | ConstantFloating fc ->
      Pp_ail.pp_floatingConstant fc
  | ConstantCharacter cc ->
      Pp_ail.pp_characterConstant cc
 | ConstantArray (elem_ty, csts) ->
     P.braces (comma_list pp_constant csts)
 | ConstantStruct (tag_sym, xs) ->
     P.parens (!^ "struct" ^^^ Pp_ail.pp_id ~is_human:true tag_sym) ^^ P.braces (
       comma_list (fun (memb_ident, cst) ->
         P.dot ^^ Pp_symbol.pp_identifier memb_ident ^^ P.equals ^^^ pp_constant cst
       ) xs
     )
 | ConstantUnion (tag_sym, memb_ident, cst) ->
   P.parens (!^ "union" ^^^ Pp_ail.pp_id ~is_human:true tag_sym)
   ^^ P.braces (P.dot ^^ Pp_symbol.pp_identifier memb_ident ^^ P.equals ^^^ pp_constant cst)
| ConstantPredefined PConstantFalse ->
    pp_keyword "false"
| ConstantPredefined PConstantTrue ->
    pp_keyword "true"

let pp_stringLiteral (pref_opt, strs) =
  let strs = List.concat (List.map snd strs) in
  (P.optional Pp_ail.pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Bold; Cyan] (fun () -> P.dquotes (!^ (String.concat "" strs)))

let empty_qs =
  { const    = false
  ; restrict = false
  ; volatile = false
  }

let pp_alignment = function
  | AlignInteger n ->
      !^ "align as" ^^ P.colon ^^^ !^ (String_nat_big_num.string_of_decimal n)
  | AlignType ty ->
      !^ "align as" ^^ P.colon ^^^ P.squotes (pp_ctype no_qualifiers ty)

let dtree_of_binding (i, ((_, sd, is_reg), align_opt, qs, ty)) =
  Dleaf (Pp_ail.pp_id i
         ^^^ Pp_ail.pp_storageDuration sd
         ^^^ pp_cond is_reg (pp_type_keyword "register") (P.squotes (pp_ctype qs ty))
         ^^  P.optional (fun z -> P.space ^^ P.brackets (pp_alignment z)) align_opt)

let rec dtree_of_expression pp_annot expr =
  let rec self (AnnotatedExpression (annot, std_annots, loc, expr_)) =
    let pp_std_annot =
      match std_annots with
        | [] -> P.empty
        | _  -> pp_ansi_format [Bold] (fun () -> P.brackets (semi_list P.string std_annots)) in
    let pp_expr_ctor str =
      pp_std_annot ^^^ pp_stmt_ctor str ^^^ Cerb_location.pp_location ~clever:true loc ^^^ pp_annot annot in
    let pp_implicit_ctor str =
      pp_std_annot ^^^ !^ (ansi_format [Bold; Red] str) ^^^ Cerb_location.pp_location ~clever:true loc ^^^ pp_annot annot in
    
    let pp_cabs_id = Pp_symbol.pp_identifier in
    let dtree_of_generic_association = function
      | AilGAtype (ty, e) ->
          let d_ctor = pp_expr_ctor "AilGAtype" in
          Dnode ( d_ctor ^^^ P.squotes (pp_ctype empty_qs ty)
                , [self e] )
      | AilGAdefault e ->
          let d_ctor = pp_expr_ctor "AilGAdefault" in
          Dnode ( d_ctor, [self e] )
    in
    let dtree_of_field (cid, e_opt) =
      match e_opt with
      | Some e -> Dnode (pp_cabs_id cid, [self e])
      | None   -> Dleaf (pp_cabs_id cid)
    in
    begin match expr_ with
      | AilEunary (uop, e) ->
          let d_ctor = pp_expr_ctor "AilEunary" in
          Dnode ( d_ctor ^^^ P.squotes (Pp_ail.pp_unaryOperator uop)
                , (*add_std_annot*) [self e] )
      | AilEbinary (e1, bop, e2) ->
          let d_ctor = pp_expr_ctor "AilEbinary" in
          let d_e1 = self e1 in
          let d_e2 = self e2 in
          Dnode ( d_ctor ^^^ P.squotes (Pp_ail.pp_binaryOperator bop)
                , (*add_std_annot*) [ d_e1; d_e2 ] )
      | AilEassign (e1, e2) ->
          let d_ctor = pp_expr_ctor "AilEassign" in
          let d_e1 = self e1 in
          let d_e2 = self e2 in
          Dnode ( d_ctor
                , (*add_std_annot*) [ d_e1; d_e2 ] )
      | AilEcompoundAssign (e1, aop, e2) ->
          let d_ctor = pp_expr_ctor "AilEcompoundAssign" in
          let d_e1 = self e1 in
          let d_e2 = self e2 in
          Dnode ( d_ctor ^^^ P.squotes (Pp_ail.pp_arithmeticOperator aop)
                , (*add_std_annot*) [ d_e1; d_e2 ] )
      | AilEcond (e1, None, e3) ->
          let d_ctor = pp_expr_ctor "AilEcond" ^^^ P.parens (!^ "GNU ?:") in
          let d_e1 = self e1 in
          let d_e3 = self e3 in
          Dnode ( d_ctor
                , (*add_std_annot*) [ d_e1; d_e3 ] )
      | AilEcond (e1, Some e2, e3) ->
          let d_ctor = pp_expr_ctor "AilEcond" in
          let d_e1 = self e1 in
          let d_e2 = self e2 in
          let d_e3 = self e3 in
          Dnode ( d_ctor
                , (*add_std_annot*) [ d_e1; d_e2; d_e3 ] )
      | AilEcast (qs, ty, e) ->
          let d_ctor = pp_expr_ctor "AilEcast" in
          Dnode ( d_ctor ^^^ P.squotes (pp_ctype qs ty)
                , (*add_std_annot*) [self e] )
      | AilEcall (e, es) ->
          let d_ctor = pp_expr_ctor "AilEcall" in
          Dnode ( d_ctor
                , (*add_std_annot*) (self e :: List.map self es) )
      | AilEassert e ->
          let d_ctor = pp_expr_ctor "AilEassert" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEoffsetof (ty, ident) ->
          let d_ctor = pp_expr_ctor "AilEoffsetof" in
          (*add_std_to_leaf*)Dleaf ( d_ctor ^^^ pp_cabs_id ident ^^^
                P.squotes (pp_ctype empty_qs ty))
      | AilEgeneric (e, gas) ->
          let d_ctor = pp_expr_ctor "AilEgeneric" in
          Dnode ( d_ctor
                , (*add_std_annot*) (self e :: List.map dtree_of_generic_association
                                   gas) )
      | AilEarray (is_str, ty, e_opts) ->
          let d_ctor = pp_expr_ctor "AilEarray" in
          Dnode ( d_ctor ^^^ (if is_str then !^ (ansi_format [Cyan] "str") ^^ P.space else P.empty) ^^
                  P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) (filter_opt_list
                                   (List.map (option None self) e_opts)) )
      | AilEstruct (tag_sym, xs) ->
          let d_ctor = pp_expr_ctor "AilEstruct" in
          Dnode ( d_ctor ^^^ Pp_ail.pp_id ~is_human:true tag_sym
                , (*add_std_annot*) (List.map dtree_of_field xs) )
      | AilEunion (tag_sym, memb_ident, e_opt) ->
          let d_ctor = pp_expr_ctor "AilEunion" in
          Dnode ( d_ctor ^^^ Pp_ail.pp_id ~is_human:true tag_sym
                , (*add_std_annot*) [dtree_of_field (memb_ident, e_opt)] )
      | AilEcompound (qs, ty, e) ->
          let d_ctor = pp_expr_ctor "AilEcompound" in
          Dnode ( d_ctor ^^^ pp_qualifiers qs ^^^ P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) [self e] )
      | AilEmemberof (e, ident) ->
          let d_ctor = pp_expr_ctor "AilEmemberof" in
          Dnode ( d_ctor ^^^ pp_cabs_id ident
                , (*add_std_annot*) [self e] )
      | AilEmemberofptr (e, ident) ->
          let d_ctor = pp_expr_ctor "AilEmemberofptr" in
          Dnode ( d_ctor ^^^ pp_cabs_id ident
                , (*add_std_annot*) [self e] )
      | AilEbuiltin b ->
          (*add_std_to_leaf*)Dleaf ( pp_expr_ctor "AilEbuiltin" ^^^ Pp_ail.pp_ail_builtin b )
      | AilEstr lit ->
          (*add_std_to_leaf*)Dleaf ( pp_expr_ctor "AilEstr" ^^^ pp_stringLiteral lit )
      | AilEconst c ->
          (*add_std_to_leaf*)Dleaf ( pp_expr_ctor "AilEconst" ^^^ pp_constant c )
      | AilEident sym ->
          (*add_std_to_leaf*)
          let d_ctor = pp_expr_ctor "AilEident" in
          Dleaf ( d_ctor ^^^ pp_symbol sym )
      | AilEsizeof (qs, ty) ->
          (*add_std_to_leaf*)
          Dleaf ( pp_expr_ctor "AilEsizeof" ^^^ P.squotes (pp_ctype qs ty) )
      | AilEsizeof_expr e ->
          let d_ctor = pp_expr_ctor "AilEsizeof_expr" in
          Dnode ( d_ctor, (*add_std_annot*) [self e] )
      | AilEalignof (qs, ty) ->
          (*add_std_to_leaf*)
          Dleaf ( pp_expr_ctor "AilEalignof" ^^^ P.squotes (pp_ctype qs ty) )
      | AilEannot (ty, e) ->
          let d_ctor = pp_expr_ctor "AilEannot" in
          Dnode ( d_ctor ^^^ P.squotes (pp_ctype empty_qs ty),
                  (*add_std_annot*) [self e] )
      | AilEva_start (e, sym) ->
          let d_ctor = pp_expr_ctor "AilEva_start" in
          Dnode ( d_ctor ^^^ Pp_ail.pp_id sym
                , (*add_std_annot*) [self e] )
      | AilEva_copy (e1, e2) ->
          let d_ctor = pp_expr_ctor "AilEva_copy" in
          let d_e1 = self e1 in
          let d_e2 = self e2 in
          Dnode ( d_ctor, (*add_std_annot*)[ d_e1; d_e2 ] )
      | AilEva_arg (e, ty) ->
          let d_ctor = pp_expr_ctor "AilEva_arg" in
          Dnode ( d_ctor ^^^ P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) [self e] )
      | AilEva_end e ->
          let d_ctor = pp_expr_ctor "AilEva_end" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEbmc_assume e ->
          let d_ctor = pp_expr_ctor "AilEbmc_assume" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEreg_load r ->
          Dleaf ( pp_expr_ctor "AilEreg_load" ^^^ !^("r" ^ string_of_int r))
      | AilEprint_type e ->
          let d_ctor = pp_expr_ctor "AilEprint_type" in
          Dnode ( d_ctor, (*add_std_annot*) [self e])
      | AilErvalue e ->
          let d_ctor = pp_implicit_ctor "AilErvalue" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEarray_decay e ->
          let d_ctor = pp_implicit_ctor "AilEarray_decay" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEfunction_decay e ->
          let d_ctor = pp_implicit_ctor "AilEfunction_decay" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEatomic e ->
          let d_ctor = pp_implicit_ctor "AilEatomic" in
          Dnode ( d_ctor
                , (*add_std_annot*) [self e] )
      | AilEgcc_statement (bs, ss) ->
          Dnode ( pp_expr_ctor "AilEgcc_statement"
                , Dnode (pp_ctor "Bindings", List.map dtree_of_binding bs) :: List.map (dtree_of_statement pp_annot) ss )
    end in
  self expr

and dtree_of_statement pp_annot (AnnotatedStatement (loc, attrs, stmt_)) =
  let dtree_of_expression = dtree_of_expression pp_annot in
  let dtree_of_statement = dtree_of_statement pp_annot in
  with_attributes attrs
  begin match stmt_ with
    | AilSskip ->
        Dleaf (pp_stmt_ctor "AilSskip")
    | AilSexpr e ->
        Dnode ( pp_stmt_ctor "AilSexpr"
              , [dtree_of_expression e] )
    | AilSblock (bs, ss) ->
        Dnode ( pp_stmt_ctor "AilSblock"
              , Dnode (pp_ctor "Bindings", List.map dtree_of_binding bs)
                :: List.map dtree_of_statement ss )
    | AilSif (e, s1, s2) ->
        let d_e  = dtree_of_expression e in
        let d_s1 = dtree_of_statement s1 in
        let d_s2 = dtree_of_statement s2 in
        Dnode ( pp_stmt_ctor "AilSif", [ d_e; d_s1; d_s2 ] )
    | AilSwhile (e, s, _) ->
        let d_e = dtree_of_expression e in
        let d_s = dtree_of_statement s  in
        Dnode ( pp_stmt_ctor "AilSwhile", [ d_e; d_s ] )
    | AilSdo (s, e, _) ->
        let d_s = dtree_of_statement s  in
        let d_e = dtree_of_expression e in
        Dnode ( pp_stmt_ctor "AilSdo", [ d_s; d_e ] )
    | AilSbreak ->
        Dleaf (pp_stmt_ctor "AilSbreak")
    | AilScontinue ->
        Dleaf (pp_stmt_ctor "AilScontinue")
    | AilSreturnVoid ->
        Dleaf (pp_stmt_ctor "AilSreturnVoid")
    | AilSreturn e ->
        Dnode ( pp_stmt_ctor "AilSreturn", [dtree_of_expression e] )
    | AilSswitch (e, s) ->
        let d_e = dtree_of_expression e in
        let d_s = dtree_of_statement s  in
        Dnode ( pp_stmt_ctor "AilSswitch", [ d_e; d_s ] )
    | AilScase (n, s) ->
        Dnode ( pp_stmt_ctor "AilScase" ^^^ (!^ (Z.to_string n))
              , [dtree_of_statement s] )
    | AilScase_rangeGNU (n1, n2, s) ->
        Dnode ( pp_stmt_ctor "AilScase_rangeGNU" ^^^ !^ (Z.to_string n1 ^ " ... " ^ Z.to_string n2)
              , [dtree_of_statement s] )
    | AilSdefault s ->
        Dnode ( pp_stmt_ctor "AilSdefault", [dtree_of_statement s] )
    | AilSlabel (sym, s, _) ->
        Dnode ( pp_stmt_ctor "AilSlabel" ^^^ Pp_ail.pp_id sym
              , [dtree_of_statement s] )
    | AilSgoto sym ->
        Dleaf ( pp_stmt_ctor "AilSgoto" ^^^ Pp_ail.pp_id sym )
    | AilSdeclaration xs ->
        Dnode ( pp_stmt_ctor "AilSdeclaration"
              , List.map (fun (sym, e_opt) ->
                    Dnode (pp_stmt_ctor "Symbol" ^^^ Pp_ail.pp_id sym
                          , [Option.fold ~none:(Dleaf !^ "NOINIT") ~some:dtree_of_expression e_opt])
                ) xs )
    | AilSpar ss ->
        Dnode (pp_stmt_ctor "AilSpar"
               , List.map (fun s -> dtree_of_statement s) ss)
    | AilSreg_store (r, e) ->
        Dnode (pp_stmt_ctor "AilSreg_store" ^^^ !^("r" ^ string_of_int r)
              , [dtree_of_expression e])
    | AilSmarker (n, s) ->
        Dnode ( pp_stmt_ctor "AilSmarker" ^^^ !^("#" ^ string_of_int n)
              , [dtree_of_statement s] )
  end

let dtree_of_function_definition pp_annot (fun_sym, (loc, _, attrs, param_syms, stmt)) =
  let param_dtrees = [] in
  let pp_loc = Cerb_location.pp_location ~clever:true loc in
  Dnode ( pp_decl_ctor "FunctionDecl" ^^^ pp_loc ^^^ Pp_ail.pp_id fun_sym
        , add_dtree_of_attributes attrs (param_dtrees @ [dtree_of_statement pp_annot stmt]) )

let pp_storageDuration = function
  | Static    -> pp_type_keyword "static"
  | Thread    -> pp_type_keyword "thread"
  | Automatic -> pp_type_keyword "automatic"

let dtree_of_typedef_attributes (sym, attrs) =
  with_attributes attrs begin
    Dleaf (pp_symbol sym)
  end


let dtree_of_declaration (i, (_, decl_attrs, decl)) =
  let pp_storage (sd, isRegister) =
    pp_storageDuration sd ^^
    (if isRegister then P.space ^^ pp_type_keyword "register" else P.empty)
  in
  with_attributes decl_attrs begin
    match decl with
    | Decl_object (msd, align_opt, qs, cty) ->
        Dleaf (pp_decl_ctor "Decl_object" ^^^
               Pp_ail.pp_id_obj i  ^^^
               P.squotes (pp_storage msd ^^^ pp_ctype qs cty) ^^
               P.optional (fun z -> P.space ^^ P.brackets (pp_alignment z)) align_opt)
    | Decl_function (_, (qs, cty), params, is_var, is_inline, is_noreturn) ->
        Dleaf (pp_decl_ctor "Decl_function" ^^^
               Pp_ail.pp_id_func i ^^^
               Cerb_colour.pp_ansi_format [Green] begin fun () -> 
                 P.squotes (
                   (pp_cond is_inline !^"inline"
                   (pp_cond is_noreturn !^"_Noreturn"
                   (pp_ctype_human empty_qs
                      (Ctype ([], Function ((qs, cty), params, is_var))))))
                 )
               end)
  end


let dtree_of_tag_definition (i, (tagdef_loc, def_attrs, tag)) =
  let dleaf_of_field (i, (attrs, align_opt, qs, ty)) =
    with_attributes attrs begin
      Dleaf (Pp_symbol.pp_identifier i ^^^ P.squotes (pp_ctype qs ty) ^^
             P.optional (fun z -> P.space ^^ P.brackets (pp_alignment z)) align_opt)
    end
  in with_attributes def_attrs begin match tag with
    | StructDef (fs_, flexible_opt) ->
        let fs = match flexible_opt with
          | None ->
              fs_
          | Some (FlexibleArrayMember (attrs, ident, qs, elem_ty)) ->
              fs_ @ [(ident, (attrs, None, qs, Ctype ([], Array (elem_ty, None))))] in
        Dnode ( pp_ctor "StructDef" ^^^ Cerb_location.pp_location ~clever:false tagdef_loc ^^^
                Pp_ail.pp_id ~is_human:true i
              , List.map dleaf_of_field fs)


    | UnionDef fs ->
        Dnode ( pp_ctor "UnionDef" ^^^ Cerb_location.pp_location ~clever:false tagdef_loc ^^^
                Pp_ail.pp_id ~is_human:true i
              , List.map dleaf_of_field fs)
  end

let dtree_of_object_definition pp_annot (i, e) =
  Dnode (pp_ctor "Def_object" ^^^ Pp_ail.pp_id i, [dtree_of_expression pp_annot e])

let dtree_of_static_assertions pp_annot (e, lit) =
  Dnode (pp_ctor "Static_assert"
        , [ dtree_of_expression pp_annot e;
            Dleaf (pp_stringLiteral lit) ])

let dtree_of_program pp_annot (_, sigm) =
  Dnode ( pp_decl_ctor "AilSigma" ,
          [ Dnode (pp_decl_ctor "AilTypedefAttributes"
                  , List.map dtree_of_typedef_attributes (Pmap.bindings_list sigm.typedef_attributes))
          ; Dnode (pp_decl_ctor "AilDeclarations"
                  , List.map dtree_of_declaration sigm.declarations)
          ; Dnode (pp_ctor "AilTagDefinitions"
                  , List.map dtree_of_tag_definition sigm.tag_definitions)
          ; Dnode (pp_ctor "AilObjectDefinitions"
                  , List.map (dtree_of_object_definition pp_annot)
                      sigm.object_definitions)
          ; Dnode ( pp_ctor "AilFunctionDefinitions"
                  , List.map (dtree_of_function_definition pp_annot)
                      sigm.function_definitions )
          ; Dnode (pp_ctor "AilStaticAssertions"
                  , List.map (dtree_of_static_assertions pp_annot)
                      sigm.static_assertions)
          ; Dnode (pp_ctor "AilCNpredicates"
                  , List.map Cn_ocaml.PpAil.dtree_of_cn_predicate sigm.cn_predicates)
          ] )

let pp_annot gtc =
  let mk_pp_alias (Ctype (_, ty_)) =
    match ty_ with
      | Basic (Integer ity) ->
          let ity' = Ocaml_implementation.(normalise_integerType (get ()) ity) in
          begin if not (Ctype.integerTypeEqual ity ity') then
            fun z -> z ^^ P.colon ^^ P.squotes (Pp_ail.pp_basicType (Integer ity'))
          else
            Fun.id
          end
     | _ -> Fun.id in
  match gtc with
    | GenLValueType (qs, ty, isRegister) ->
        let qs_ty_doc =
          (* TODO: do the colour turn off in pp_ansi_format *)
          let saved = !Cerb_colour.do_colour in
          Cerb_colour.do_colour := false;
          let ret = mk_pp_alias ty (P.squotes (pp_ctype_human qs ty)) in
          Cerb_colour.do_colour := saved;
          ret in
        pp_ansi_format [Green] (fun () -> qs_ty_doc) ^^^
        !^ (ansi_format [Cyan] "lvalue") ^^
        (if isRegister then P.space ^^ !^ "register" else P.empty)
    | GenRValueType gty ->
        pp_ansi_format [Green] (fun () -> 
          P.squotes (Pp_ail.pp_genType gty)
        )

let filter_external_decl (id, sigma) =
  let pred (_, (loc, _, _)) = Cerb_location.from_main_file loc in
  (id, { sigma with declarations = List.filter pred sigma.declarations} )

(* let pp_loop_attributes xs =
  let pp_env env =
    Pmap.fold (fun ident sym_opt acc ->
      Pp_symbol.pp_identifier ident ^^^ P.equals ^^ P.rangle ^^^ P.optional pp_symbol sym_opt ^^ P.comma ^^^ acc
    ) env P.empty in
  Pmap.fold (fun key (env, _) acc ->
    !^ (string_of_int key) ^^^ P.equals ^^ P.rangle ^^^ pp_env env ^^ P.comma ^^ acc
  ) xs P.empty *)

let pp_program do_colour show_include ail_prog =
  Cerb_colour.do_colour := do_colour && Unix.isatty Unix.stdout;
  let filtered_ail_prog = if show_include then ail_prog else filter_external_decl ail_prog in
  (* pp_loop_attributes (snd ail_prog).loop_attributes ^^ P.break 1 ^^ *)
  pp_doc_tree (dtree_of_program (fun _ -> P.empty) filtered_ail_prog)

(* For debugging: prints all the type annotations *)
let pp_program_with_annot (p: GenTypes.genTypeCategory ail_program) : PPrint.document =
  pp_doc_tree (dtree_of_program pp_annot p)
