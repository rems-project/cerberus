open AilSyntax
open AilTypes
open GenTypes

open Pp_prelude
open Pp_ast
open Colour

open Pp_ail

module P = PPrint

let isatty = ref false


open Lem_pervasives
open Either


let pp_symbol sym =
  !^ (ansi_format [Bold; Cyan] (Pp_symbol.to_string_pretty sym))



let rec pp_constant = function
  | ConstantIndeterminate ty ->
      (* NOTE: this is not in C11 *)
      pp_keyword "indet" ^^ P.parens (pp_ctype no_qualifiers ty)
  | ConstantNull ->
      pp_const "NULL"
  | ConstantInteger ic ->
      pp_integerConstant ic
  | ConstantFloating fc ->
      pp_floatingConstant fc
  | ConstantCharacter cc ->
      pp_characterConstant cc
 | ConstantArray csts ->
     P.braces (comma_list pp_constant csts)
 | ConstantStruct (tag_sym, xs) ->
     P.parens (!^ "struct" ^^^ pp_id tag_sym) ^^ P.braces (
       comma_list (fun (memb_ident, cst) ->
         P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^ P.equals ^^^ pp_constant cst
       ) xs
     )
 | ConstantUnion (tag_sym, memb_ident, cst) ->
     P.parens (!^ "union" ^^^ pp_id tag_sym) ^^ P.braces (P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^ P.equals ^^^ pp_constant cst)







let pp_stringLiteral (pref_opt, strs) =
  (P.optional pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Bold; Cyan] (P.dquotes (!^ (String.concat "" strs)))


let dtree_of_expression pp_annot expr =
  let rec self (AnnotatedExpression (annot, _, loc, expr_)) =
    let pp_stmt_ctor str =
      pp_stmt_ctor str ^^^ pp_annot annot in
    let pp_implicit_ctor str =
      !^ (ansi_format [Bold; Red] str) ^^^ pp_annot annot in
    begin match expr_ with
      | AilEunary (uop, e) ->
          Dnode ( pp_stmt_ctor "AilEunary" ^^^ P.squotes (pp_unaryOperator uop)
                , [self e] )
      | AilEbinary (e1, bop, e2) ->
          Dnode ( pp_stmt_ctor "AilEbinary" ^^^ P.squotes (pp_binaryOperator bop)
                , [self e1; self e2] )
      | AilEassign (e1, e2) ->
          Dnode ( pp_stmt_ctor "AilEassign"
                , [self e1; self e2] )
      | AilEcompoundAssign (e1, aop, e2) ->
          Dnode ( pp_stmt_ctor "AilEcompoundAssign" ^^^ P.squotes (pp_arithmeticOperator aop)
                , [self e1; self e2] )
      | AilEcond (e1, e2, e3) ->
          Dnode ( pp_stmt_ctor "AilEcond"
                , [self e1; self e2; self e3] )
      | AilEcast (qs, ty, e) ->
          Dnode ( pp_stmt_ctor "AilEcast" ^^^ !^" TODO"
                , [self e] )
      | AilEcall (e, es) ->
          Dnode ( pp_stmt_ctor "AilEcall" ^^^ !^" TODO"
                , [] )
      | AilEassert e ->
          Dnode ( pp_stmt_ctor "AilEassert" ^^^ !^" TODO"
                , [self e] )
      | AilEoffsetof (ty, ident) ->
          Dnode ( pp_stmt_ctor "AilEoffsetof" ^^^ !^" TODO"
                , [] )
      | AilEgeneric (e, gas) ->
          Dnode ( pp_stmt_ctor "AilEgeneric" ^^^ !^" TODO"
                , [] )
      | AilEarray (ty, e_opts) ->
          Dnode ( pp_stmt_ctor "AilEarray" ^^^ !^" TODO"
                , [] )
      | AilEstruct (tag_sym, xs) ->
          Dnode ( pp_stmt_ctor "AilEstruct" ^^^ !^" TODO"
                , [] )
      | AilEunion (tag_sym, memb_ident, e_opt) ->
          Dnode ( pp_stmt_ctor "AilEunion" ^^^ !^" TODO"
                , [] )
      | AilEcompound (ty, e) ->
          Dnode ( pp_stmt_ctor "AilEcompound" ^^^ !^" TODO"
                , [] )
      | AilEmemberof (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberof" ^^^ !^" TODO"
                , [] )
      | AilEmemberofptr (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberofptr" ^^^ !^" TODO"
                , [] )
      | AilEbuiltin str ->
          Dnode ( pp_stmt_ctor "AilEbuiltin" ^^^ !^" TODO"
                , [] )
      | AilEstr lit ->
          Dleaf ( pp_stmt_ctor "AilEstr" ^^^ pp_stringLiteral lit )
      | AilEconst c ->
          Dnode ( pp_stmt_ctor "AilEconst" ^^^ !^" TODO"
                , [] )
      | AilEident sym ->
          Dleaf ( pp_stmt_ctor "AilEident" ^^^ pp_symbol sym )
      | AilEsizeof (qs, ty) ->
          failwith "2"
      | AilEsizeof_expr e ->
          Dnode ( pp_stmt_ctor "AilEsizeof_expr"
                , [self e] )
      | AilEalignof (qs, ty) ->
          failwith "3"
      | AilEannot (_, e) ->
          failwith "4"
      | AilEva_start (e, sym) ->
          failwith "5"
      | AilEva_arg (e, ty) ->
          failwith "6"
      | AilEprint_type e ->
          failwith "7"
      | AilErvalue e ->
          Dnode ( pp_implicit_ctor "AilErvalue"
                , [self e] )
      | AilEarray_decay e ->
          Dnode ( pp_implicit_ctor "AilEarray_decay"
                , [self e] )
      | AilEfunction_decay e ->
          Dnode ( pp_implicit_ctor "AilEfunction_decay"
                , [self e] )
    end in
  self expr

and dtree_of_generic_association = function
  | AilGAtype (ty, e) ->
      failwith "8"
  | AilGAdefault e ->
      failwith "9"


(*
let rec pp_statement_aux pp_annot (AnnotatedStatement (_, stmt)) =
  let pp_statement = pp_statement_aux pp_annot in
  match stmt with
    | AilSskip ->
        P.semi
    | AilSexpr e ->
        pp_expression_aux pp_annot e ^^ P.semi
    | AilSblock ([], []) ->
        P.lbrace ^^ P.rbrace
    | AilSblock ([], ss) ->
        P.lbrace ^^ P.nest 2 (
          P.break 1 ^^ (P.separate_map (P.break 1) pp_statement ss)
        ) ^^ P.rbrace
    | AilSblock (bindings, ss) ->
        let block =
          P.separate_map
            (P.semi ^^ P.break 1)
            (fun (id, (dur_reg_opt, qs, ty)) ->
              if !Debug_ocaml.debug_level > 5 then
                (* printing the types in a human readable format *)
                P.parens (
                  P.optional (fun (dur, isRegister) ->
                    (fun z -> if isRegister then pp_keyword "register" ^^^ z else z)
                      (pp_storageDuration dur)
                  ) dur_reg_opt ^^^ pp_ctype_human qs ty
                ) ^^^ pp_id_obj id
              else
                pp_ctype qs ty ^^^ pp_id_obj id
               ) bindings ^^ P.semi ^^ P.break 1 ^^
          P.separate_map (P.break 1) pp_statement ss in
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
    | AilSif (e, s1, s2) ->
        pp_keyword "if" ^^^ P.parens (pp_expression_aux pp_annot e) ^/^
          P.nest 2 (pp_statement s1) ^^^
        pp_keyword "else" ^/^
          pp_statement s2
    | AilSwhile (e, s) ->
        pp_keyword "while" ^^^ P.parens (pp_expression_aux pp_annot e) ^^^ pp_statement s
    | AilSdo (s, e) ->
        pp_keyword "do" ^^^ pp_statement s ^^^ pp_keyword "while" ^^^ P.parens (pp_expression_aux pp_annot e)
    | AilSbreak ->
        pp_keyword "break" ^^ P.semi
    | AilScontinue ->
        pp_keyword "continue" ^^ P.semi
    | AilSreturnVoid ->
        pp_keyword "return" ^^ P.semi
    | AilSreturn e ->
        pp_keyword "return" ^^^ pp_expression_aux pp_annot e ^^ P.semi
    | AilSswitch (e, s) ->
        pp_keyword "switch" ^^^ P.parens (pp_expression_aux pp_annot e) ^/^ pp_statement s
    | AilScase (ic, s) ->
        pp_keyword "case" ^^^ pp_integerConstant ic ^^ P.colon ^/^ pp_statement s
    | AilSdefault s ->
        pp_keyword "default" ^^ P.colon ^/^ pp_statement s
    | AilSlabel (l, s) ->
        pp_id_label l ^^ P.colon ^/^ pp_statement s
    | AilSgoto l ->
        pp_keyword "goto" ^^^ pp_id_label l ^^ P.semi
    | AilSdeclaration [] ->
        pp_comment "// empty decl"
    (* TODO: looks odd *)
    | AilSdeclaration defs ->
        comma_list (fun (id, e) -> pp_id_obj id ^^^ P.equals ^^^ pp_expression_aux pp_annot e) defs ^^
        P.semi ^^^ pp_comment "// decl"
    | AilSpar ss ->
        P.lbrace ^^ P.lbrace ^^ P.lbrace ^^ P.nest 2 (
          P.break 1 ^^ P.separate_map (P.break 1 ^^ !^ "|||" ^^ P.break 1) pp_statement ss
        ) ^/^ P.rbrace ^^ P.rbrace ^^ P.rbrace


let pp_static_assertion pp_annot (e, lit) =
  pp_keyword "_Static_assert" ^^ P.parens (pp_expression_aux pp_annot e ^^ P.comma ^^^ pp_stringLiteral lit)


let pp_tag_definition (tag, def) =
  match def with
    | StructDef ident_qs_tys ->
        pp_keyword "struct" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, (qs, ty)) ->
              pp_ctype qs ty ^^^ Pp_cabs.pp_cabs_identifier ident
            ) ident_qs_tys
          ) ^^ P.break 1
        ) ^^ P.semi
    | UnionDef ident_qs_tys ->
        pp_keyword "union" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, (qs, ty)) ->
              pp_ctype qs ty ^^^ Pp_cabs.pp_cabs_identifier ident
            ) ident_qs_tys
          ) ^^ P.break 1
        ) ^^ P.semi

*)


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
        Dnode ( pp_stmt_ctor "AilSblock" ^^^ !^ "TODO bindings"
              , List.map dtree_of_statement ss )
    | AilSif (e, s1, s2) ->
        Dnode ( pp_stmt_ctor "AilSif"
              , [dtree_of_expression e; dtree_of_statement s1; dtree_of_statement s2] )
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
        failwith "11"
    | AilSdefault s ->
        Dnode ( pp_stmt_ctor "AilSdefault"
              , [dtree_of_statement s] )
    | AilSlabel (sym, s) ->
        failwith "12"
    | AilSgoto sym ->
        failwith "13"
    | AilSdeclaration xs ->
        Dnode ( pp_stmt_ctor "AilSdeclaration"
              , List.map (fun (sym, e) ->
                  Dnode (pp_stmt_ctor "Symbol" ^^^ pp_id sym, [dtree_of_expression e])
                ) xs )
    | AilSpar ss ->
        failwith "15"



let dtree_of_function_definition pp_annot (fun_sym, (param_syms, stmt)) =
  let param_dtrees =
    [] in
  Dnode ( pp_id fun_sym
        , param_dtrees @ [dtree_of_statement pp_annot stmt] )

(*
Context.context identifier (list identifier * statement 'a);
*)

let pp_program_aux pp_annot (_, sigm) =
  (* Static assersions *)

(* TODO KKKK
  begin match sigm.static_assertions with
    | [] ->
        P.empty
    | xs ->
        P.separate_map (P.break 1 ^^ P.break 1) (pp_static_assertion pp_annot) xs ^^ P.break 1 ^^ P.break 1 ^^ P.break 1 
  end ^^
  
  (* Tag declarations *)
  begin match sigm.tag_definitions with
    | [] ->
        P.empty
    | xs ->
        P.separate_map (P.break 1 ^^ P.break 1) pp_tag_definition xs ^^ P.break 1 ^^ P.break 1 ^^ P.break 1
  end ^^

*)
  
  Dnode ( pp_ctor "AilSigma"
        , [ Dnode (pp_ctor "AilDeclarations", [])
          ; Dnode (pp_ctor "AilTagDefinitions", [])
          ; Dnode (pp_ctor "AilObjectDeclarations", [])
          ; Dnode ( pp_ctor "AilFunctionDefinitions"
                  , List.map (dtree_of_function_definition pp_annot) sigm.function_definitions )
          ; Dnode (pp_ctor "AilStaticAssertions", [])
          ] )
  


(*
  P.separate_map (P.break 1 ^^ P.hardline) (fun (sym, decl) ->
    match decl with
      | Decl_object (sd, qs, ty) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          (if !isatty then !^ "\x1b[31m" else P.empty) ^^
          !^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ (pp_ctype_human qs ty) ^^
          (if !isatty then !^ "\x1b[0m" else P.empty) ^^ P.hardline ^^
          
          (if !Debug_ocaml.debug_level > 5 then
            (* printing the types in a human readable format *)
            pp_id_obj sym ^^ P.colon ^^^ P.parens (pp_ctype_human qs ty)
          else
            pp_ctype_declaration (pp_id_obj sym) qs ty) ^^
          
          P.optional (fun e ->
            P.space ^^ P.equals ^^^ pp_expression_aux pp_annot e
          ) (Context.lookup identifierEqual sigm.object_definitions sym) ^^ P.semi
      
      | Decl_function (has_proto, (ret_qs, ret_ty), params, is_variadic, is_inline, is_Noreturn) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          (if !isatty then !^ "\x1b[31m" else P.empty) ^^
          !^ "// declare" ^^^ pp_id sym ^^^
          (if has_proto then !^ "WITH PROTO " else P.empty) ^^
          !^ "as" ^^^ pp_ctype_human no_qualifiers (Function (has_proto, (ret_qs, ret_ty), params, is_variadic)) ^^
          (if !isatty then !^ "\x1b[0m" else P.empty) ^^ P.hardline ^^
          
          (fun k -> if is_inline   then !^ "inline"    ^^^ k else k) (
            (fun k -> if is_Noreturn then !^ "_Noreturn" ^^^ k else k) (
              begin
                if !Debug_ocaml.debug_level > 5 then
                  (* printing the types in a human readable format *)
                  pp_ctype_human ret_qs ret_ty ^^^ pp_id_func sym
                else
                  pp_ctype_declaration (pp_id_func sym) ret_qs ret_ty
              end ^^
              (match Context.lookup identifierEqual sigm.function_definitions sym with
                | Some (param_syms, stmt) ->
                    P.parens (
                      comma_list (fun (sym, (qs, ty, isRegister)) ->
                        if !Debug_ocaml.debug_level > 5 then
                          (* printing the types in a human readable format *)
                          pp_id_obj sym ^^ P.colon ^^^
                          P.parens (
                            (fun z -> if isRegister then !^ "register" ^^^ z else z)
                              (pp_ctype_human qs ty)
                          )
                        else
                          pp_ctype qs ty ^^^ pp_id_obj sym
                      ) (List.combine param_syms params) ^^
                      if is_variadic then
                        P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                      else
                        P.empty
                    ) ^^^
                    pp_statement_aux pp_annot stmt
                | None ->
                    P.parens (
                      comma_list (fun (qs, ty, isRegister) ->
                        if !Debug_ocaml.debug_level > 5 then
                          (* printing the types in a human readable format *)
                          P.parens (
                            (fun z -> if isRegister then !^ "register" ^^^ z else z)
                              (pp_ctype_human qs ty)
                          )
                        else
                          pp_ctype qs ty
                      ) params ^^
                      if is_variadic then
                        P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                      else
                        P.empty
                    ) ^^ P.semi
              )
            )
          )
    ) sigm.declarations ^^ P.hardline
*)





let pp_annot gtc =
  match gtc with
    | GenLValueType (qs, ty, isRegister) ->
        let qs_ty_doc =
          (* TODO: do the colour turn off in pp_ansi_format *)
          let saved = !Colour.do_colour in
          Colour.do_colour := false;
          let ret = P.squotes (pp_ctype qs ty) in
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




let pp_program p =
  pp_doc_tree (pp_program_aux (fun _ -> P.empty) p)

(* For debugging: prints all the type annotations *)
let pp_program_with_annot (p: GenTypes.genTypeCategory program) : PPrint.document =
  pp_doc_tree (pp_program_aux pp_annot p)
