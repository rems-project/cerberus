open AilSyntax
open AilTypes
open GenTypes

open Pp_prelude
(*open Pp_ail*)

open Pp_ast
open Colour

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



let rec pp_ctype_human qs (Ctype (_, ty)) =
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
    | Function (has_proto, (ret_qs, ret_ty), params, is_variadic) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        if not (AilTypesAux.is_unqualified qs) then
          print_endline "TODO: warning, found qualifiers in a function type (this is an UB)"; (* TODO: is it really UB? *)
        
        !^ (if is_variadic then "variadic function" else "function") ^^^
        (if has_proto then !^ "with proto " else P.empty) ^^
        P.parens (
          comma_list (fun (param_qs, param_ty, isRegister) ->
            (fun z -> if isRegister then !^ "register" ^^^ z else z)
              (pp_ctype_human param_qs param_ty)
          ) params
        ) ^^^
        !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
    | Pointer (ref_qs, ref_ty) ->
        prefix_pp_qs ^^ !^ "pointer to" ^^^ pp_ctype_human ref_qs ref_ty
    | Atomic atom_ty ->
        prefix_pp_qs ^^ !^ "atomic" ^^^ pp_ctype_human no_qualifiers atom_ty
    | Struct tag_sym ->
        prefix_pp_qs ^^ !^ "struct" ^^^ Pp_ail.pp_id tag_sym
    | Union tag_sym ->
        prefix_pp_qs ^^ !^ "union" ^^^ Pp_ail.pp_id tag_sym
    | Builtin str ->
        prefix_pp_qs ^^ P.brackets (!^ "builtin") ^^ !^ str


let rec pp_genIntegerType_raw = function
 | Concrete ity ->
     !^ "Concrete" ^^ P.brackets (Pp_ail_raw.pp_integerType_raw ity)
 | SizeT ->
     !^ "SizeT"
 | PtrdiffT ->
     !^ "PtrdiffT"
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

let pp_genType = function
 | GenVoid ->
     !^ "void"
 | GenBasic gbty ->
     pp_genBasicType_raw gbty
  | GenArray (ty, None) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_human no_qualifiers ty ^^ P.comma ^^^ !^ "None")
  | GenArray (ty, Some n) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_human no_qualifiers ty ^^ P.comma ^^^ !^ "Some" ^^ P.brackets (Pp_ail.pp_integer n))

     
 | GenFunction (has_proto, ty, params, is_variadic) ->
      !^ "GenFunction" ^^ P.brackets (
        comma_list (fun (qs, ty, isRegister) ->
          P.parens (pp_ctype_human qs ty ^^
                    P.comma ^^^ !^ (if isRegister then "true" else "false"))
        ) params ^^ P.comma ^^ !^ (if is_variadic then "true" else "false")
       )

 | GenPointer (ref_qs, ref_ty) ->
     !^ "GenPointer" ^^ P.brackets (pp_ctype_human ref_qs ref_ty)
  | GenStruct sym ->
      !^ "GenStruct" ^^ Pp_ail.pp_id sym
  | GenUnion sym ->
      !^ "GenUnion" ^^ Pp_ail.pp_id sym
  | GenAtomic ty ->
      !^ "GenAtomic" ^^ pp_ctype_human no_qualifiers ty
  | GenBuiltin str ->
      !^ "GenBuiltin" ^^ P.brackets (!^ str)



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
     P.parens (!^ "struct" ^^^ Pp_ail.pp_id tag_sym) ^^ P.braces (
       comma_list (fun (memb_ident, cst) ->
         P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^ P.equals ^^^ pp_constant cst
       ) xs
     )
 | ConstantUnion (tag_sym, memb_ident, cst) ->
   P.parens (!^ "union" ^^^ Pp_ail.pp_id tag_sym)
   ^^ P.braces (P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^ P.equals ^^^ pp_constant cst)

let pp_stringLiteral (pref_opt, strs) =
  (P.optional Pp_ail.pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Bold; Cyan] (P.dquotes (!^ (String.concat "" strs)))

let empty_qs =
  { AilTypes.const    = false
  ; AilTypes.restrict = false
  ; AilTypes.volatile = false
  }


let dtree_of_expression pp_annot expr =
  let rec self (AnnotatedExpression (annot, std_annots, loc, expr_)) =
    let pp_std_annot =
      match std_annots with
        | [] -> P.empty
        | _  -> pp_ansi_format [Bold] (P.brackets (semi_list P.string std_annots)) in

(*
    let dleaf_std_annot =
      Dleaf (pp_ctor "STD" ^^^ P.brackets (semi_list P.string std_annots))
    in
    let add_std_annot ds =
      match std_annots with
      | [] -> ds
      | _  -> dleaf_std_annot :: ds
    in
    let add_std_to_leaf pp =
      match std_annots with
      | [] -> Dleaf pp
      | _ -> Dnode (pp, [dleaf_std_annot])
    in
*)
    let pp_stmt_ctor str =
      pp_std_annot ^^^ pp_stmt_ctor str ^^^ Location_ocaml.pp_location loc ^^^ pp_annot annot in
    let pp_implicit_ctor str =
      pp_std_annot ^^^ !^ (ansi_format [Bold; Red] str) ^^^ Location_ocaml.pp_location loc ^^^ pp_annot annot in
    
    let pp_cabs_id = Pp_cabs.pp_cabs_identifier in
    let dtree_of_generic_association = function
      | AilGAtype (ty, e) ->
        Dnode ( pp_stmt_ctor "AilGAtype" ^^^ P.squotes (pp_ctype empty_qs ty),
                [self e ] )
      | AilGAdefault e ->
        Dnode ( pp_stmt_ctor "AilGAdefault", [ self e] )
    in
    let dtree_of_field (cid, e_opt) =
      match e_opt with
      | Some e -> Dnode (pp_cabs_id cid, [self e])
      | None   -> Dleaf (pp_cabs_id cid)
    in
    begin match expr_ with
      | AilEunary (uop, e) ->
          Dnode ( pp_stmt_ctor "AilEunary" ^^^ P.squotes (Pp_ail.pp_unaryOperator uop)
                , (*add_std_annot*) [self e] )
      | AilEbinary (e1, bop, e2) ->
          Dnode ( pp_stmt_ctor "AilEbinary" ^^^ P.squotes (Pp_ail.pp_binaryOperator bop)
                , (*add_std_annot*) [self e1; self e2] )
      | AilEassign (e1, e2) ->
          Dnode ( pp_stmt_ctor "AilEassign"
                , (*add_std_annot*) [self e1; self e2] )
      | AilEcompoundAssign (e1, aop, e2) ->
          Dnode ( pp_stmt_ctor "AilEcompoundAssign"
                  ^^^ P.squotes (Pp_ail.pp_arithmeticOperator aop)
                , (*add_std_annot*) [self e1; self e2] )
      | AilEcond (e1, e2, e3) ->
          Dnode ( pp_stmt_ctor "AilEcond"
                , (*add_std_annot*) [self e1; self e2; self e3] )
      | AilEcast (qs, ty, e) ->
          Dnode ( pp_stmt_ctor "AilEcast" ^^^ P.squotes (pp_ctype qs ty)
                , (*add_std_annot*) [self e] )
      | AilEcall (e, es) ->
          Dnode ( pp_stmt_ctor "AilEcall"
                , (*add_std_annot*) (self e :: List.map self es) )
      | AilEassert e ->
          Dnode ( pp_stmt_ctor "AilEassert"
                , (*add_std_annot*) [self e] )
      | AilEoffsetof (ty, ident) ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEoffsetof" ^^^ pp_cabs_id ident ^^^
                P.squotes (pp_ctype empty_qs ty))
      | AilEgeneric (e, gas) ->
          Dnode ( pp_stmt_ctor "AilEgeneric"
                , (*add_std_annot*) (self e :: List.map dtree_of_generic_association
                                   gas) )
      | AilEarray (is_str, ty, e_opts) ->
          Dnode ( pp_stmt_ctor "AilEarray" ^^^ (if is_str then !^ (ansi_format [Cyan] "str") ^^ P.space else P.empty) ^^
                  P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) (filter_opt_list
                                   (List.map (option None self) e_opts)) )
      | AilEstruct (tag_sym, xs) ->
          Dnode ( pp_stmt_ctor "AilEstruct" ^^^ Pp_ail.pp_id tag_sym
                , (*add_std_annot*) (List.map dtree_of_field xs) )
      | AilEunion (tag_sym, memb_ident, e_opt) ->
          Dnode ( pp_stmt_ctor "AilEunion" ^^^ Pp_ail.pp_id tag_sym
                , (*add_std_annot*) [dtree_of_field (memb_ident, e_opt)] )
      | AilEcompound (qs, ty, e) ->
          Dnode ( pp_stmt_ctor "AilEcompound" ^^^ pp_qualifiers qs ^^^ P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) [self e] )
      | AilEmemberof (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberof" ^^^ pp_cabs_id ident
                , (*add_std_annot*) [self e] )
      | AilEmemberofptr (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberofptr" ^^^ pp_cabs_id ident
                , (*add_std_annot*) [self e] )
      | AilEbuiltin str ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEbuiltin" ^^^ !^str )
      | AilEstr lit ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEstr" ^^^ pp_stringLiteral lit )
      | AilEconst c ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEconst" ^^^ pp_constant c )
      | AilEident sym ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEident" ^^^ pp_symbol sym )
      | AilEsizeof (qs, ty) ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEsizeof"
                            ^^^ P.squotes (pp_ctype qs ty) )
      | AilEsizeof_expr e ->
          Dnode ( pp_stmt_ctor "AilEsizeof_expr", (*add_std_annot*) [self e] )
      | AilEalignof (qs, ty) ->
          (*add_std_to_leaf*)Dleaf ( pp_stmt_ctor "AilEalignof"
                            ^^^ P.squotes (pp_ctype qs ty) )
      | AilEannot (ty, e) ->
          Dnode ( pp_stmt_ctor "AilEannot" ^^^ P.squotes (pp_ctype empty_qs ty),
                  (*add_std_annot*) [self e] )
      | AilEva_start (e, sym) ->
          Dnode ( pp_stmt_ctor "AilEva_start" ^^^ Pp_ail.pp_id sym
                , (*add_std_annot*) [self e] )
      | AilEva_arg (e, ty) ->
          Dnode ( pp_stmt_ctor "AilEva_arg" ^^^ P.squotes (pp_ctype empty_qs ty)
                , (*add_std_annot*) [self e] )
      | AilEprint_type e ->
          Dnode ( pp_stmt_ctor "AilEprint_type", (*add_std_annot*) [self e])
      | AilErvalue e ->
          Dnode ( pp_implicit_ctor "AilErvalue"
                , (*add_std_annot*) [self e] )
      | AilEarray_decay e ->
          Dnode ( pp_implicit_ctor "AilEarray_decay"
                , (*add_std_annot*) [self e] )
      | AilEfunction_decay e ->
          Dnode ( pp_implicit_ctor "AilEfunction_decay"
                , (*add_std_annot*) [self e] )
    end in
  self expr

let dtree_of_binding (i, ((_, sd, is_reg), qs, ty)) =
  Dleaf (Pp_ail.pp_id i
         ^^^ Pp_ail.pp_storageDuration sd
         ^^^ pp_cond is_reg (pp_type_keyword "register")
           (P.squotes (pp_ctype qs ty)))

let rec dtree_of_statement pp_annot (AnnotatedStatement (loc, stmt_)) =
  let dtree_of_expression = dtree_of_expression pp_annot in
  let dtree_of_statement = dtree_of_statement pp_annot in
  match stmt_ with
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
        Dnode ( pp_stmt_ctor "AilSif"
              , [dtree_of_expression e;
                 dtree_of_statement s1; dtree_of_statement s2] )
    | AilSwhile (e, s) ->
        Dnode ( pp_stmt_ctor "AilSwhile"
              , [dtree_of_expression e; dtree_of_statement s] )
    | AilSdo (s, e) ->
        Dnode ( pp_stmt_ctor "AilSdo"
              , [dtree_of_statement s; dtree_of_expression e] )
    | AilSbreak ->
          Dleaf (pp_stmt_ctor "AilSbreak")
    | AilScontinue ->
          Dleaf (pp_stmt_ctor "AilScontinue")
    | AilSreturnVoid ->
          Dleaf (pp_stmt_ctor "AilSreturnVoid")
    | AilSreturn e ->
        Dnode ( pp_stmt_ctor "AilSreturn"
              , [dtree_of_expression e] )
    | AilSswitch (e, s) ->
        Dnode ( pp_stmt_ctor "AilSswitch"
              , [dtree_of_expression e; dtree_of_statement s] )
    | AilScase (iCst, s) ->
        Dnode ( pp_stmt_ctor "AilScase" ^^^ Pp_ail.pp_integerConstant iCst
              , [dtree_of_statement s] )
    | AilSdefault s ->
        Dnode ( pp_stmt_ctor "AilSdefault"
              , [dtree_of_statement s] )
    | AilSlabel (sym, s) ->
        Dnode ( pp_stmt_ctor "AilSlabel" ^^^ Pp_ail.pp_id sym
              , [dtree_of_statement s] )
    | AilSgoto sym ->
        Dleaf ( pp_stmt_ctor "AilSgoto" ^^^ Pp_ail.pp_id sym )
    | AilSdeclaration xs ->
        Dnode ( pp_stmt_ctor "AilSdeclaration"
              , List.map (fun (sym, e) ->
                    Dnode (pp_stmt_ctor "Symbol" ^^^ Pp_ail.pp_id sym
                          , [dtree_of_expression e])
                ) xs )
    | AilSpar ss ->
        failwith "NON-STD cppmem threads"

let dtree_of_function_definition pp_annot (fun_sym, (loc, param_syms, stmt)) =
  let param_dtrees =
    [] in
  Dnode ( pp_decl_ctor "FunctionDecl" ^^^ Location_ocaml.pp_location loc ^^^ Pp_ail.pp_id fun_sym
        , param_dtrees @ [dtree_of_statement pp_annot stmt] )

let pp_storageDuration = function
  | Static    -> pp_type_keyword "static"
  | Thread    -> pp_type_keyword "thread"
  | Automatic -> pp_type_keyword "automatic"
  | Allocated -> pp_type_keyword "allocated"

let dtree_of_declaration (i, (_, decl)) =
  let pp_storage (sd, isRegister) =
    pp_storageDuration sd ^^
    (if isRegister then P.space ^^ pp_type_keyword "register" else P.empty)
  in
  match decl with
  | Decl_object (msd, qs, cty) ->
    Dleaf (pp_decl_ctor "Decl_object" ^^^
           Pp_ail.pp_id_obj i  ^^^
           P.squotes (pp_storage msd ^^^ pp_ctype qs cty))
  | Decl_function (has_proto, (qs, cty), params, is_var, is_inline, is_noreturn) ->
    Dleaf (pp_decl_ctor "Decl_function" ^^^
           Pp_ail.pp_id_func i ^^^
           Colour.pp_ansi_format [Green] begin
             P.squotes (
               (pp_cond is_inline !^"inline"
               (pp_cond is_noreturn !^"_Noreturn"
               (pp_ctype_human empty_qs
                  (Ctype ([], Function (has_proto, (qs, cty), params, is_var))))))
             )
           end)


let dtree_of_tag_definition (i, tag) =
  let dleaf_of_field (i, (qs, ty)) =
    Dleaf (Pp_cabs.pp_cabs_identifier i ^^^ P.squotes (pp_ctype qs ty))
  in match tag with
  | StructDef fs ->
    Dnode (pp_ctor "StructDef" ^^^ Pp_ail.pp_id i
          , List.map dleaf_of_field fs)
  | UnionDef fs ->
    Dnode (pp_ctor "UnionDef" ^^^ Pp_ail.pp_id i
          , List.map dleaf_of_field fs)

let dtree_of_object_definition pp_annot (i, e) =
  Dnode (pp_ctor "Def_object" ^^^ Pp_ail.pp_id i, [dtree_of_expression pp_annot e])

let dtree_of_static_assertions pp_annot (e, lit) =
  Dnode (pp_ctor "Static_assert"
        , [ dtree_of_expression pp_annot e;
            Dleaf (pp_stringLiteral lit) ])

let dtree_of_program pp_annot (_, sigm) =
  Dnode ( pp_decl_ctor "AilSigma" ,
          [ Dnode (pp_decl_ctor "AilDeclarations"
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
          ] )

let pp_annot gtc =
  match gtc with
    | GenLValueType (qs, ty, isRegister) ->
        let qs_ty_doc =
          (* TODO: do the colour turn off in pp_ansi_format *)
          let saved = !Colour.do_colour in
          Colour.do_colour := false;
          let ret = P.squotes (pp_ctype_human qs ty) in
          Colour.do_colour := saved;
          ret in
        pp_ansi_format [Green] qs_ty_doc ^^^
        !^ (ansi_format [Cyan] "lvalue") ^^
        (if isRegister then P.space ^^ !^ "register" else P.empty)
    | GenRValueType gty ->
        pp_ansi_format [Green] (
          (* TODO: do the colour turn off in pp_ansi_format *)
          let saved = !Colour.do_colour in
          Colour.do_colour := false;
          let ret = P.squotes (pp_genType gty) in
          Colour.do_colour := saved;
          ret
       )

let filter_external_decl (id, sigma) =
  let pred (_, (loc, _)) = Location_ocaml.from_main_file loc in
  (id, { sigma with declarations = List.filter pred sigma.declarations} )

let pp_program do_colour show_include ail_prog =
  Colour.do_colour := do_colour && Unix.isatty Unix.stdout;
  let filtered_ail_prog = if show_include then ail_prog else filter_external_decl ail_prog in
  pp_doc_tree (dtree_of_program (fun _ -> P.empty) filtered_ail_prog)

(* For debugging: prints all the type annotations *)
let pp_program_with_annot (p: GenTypes.genTypeCategory ail_program) : PPrint.document =
  pp_doc_tree (dtree_of_program pp_annot p)
