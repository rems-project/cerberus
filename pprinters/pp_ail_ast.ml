open AilSyntax
open AilTypes
open GenTypes

open Pp_prelude
open Pp_ast
open Colour

open Pp_ail

module P = PPrint

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
   P.parens (!^ "union" ^^^ pp_id tag_sym)
   ^^ P.braces (P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^ P.equals ^^^ pp_constant cst)

let pp_stringLiteral (pref_opt, strs) =
  (P.optional pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Bold; Cyan] (P.dquotes (!^ (String.concat "" strs)))

let rec dtree_of_ctype = function
  | Void ->
    Dleaf (pp_type_keyword "void")
  | Basic bty ->
    Dleaf (pp_basicType bty)
  | Array (cty, nopt) ->
    let pp_array = function
      | None -> pp_ctor "Array"
      | Some n -> pp_ctor "Array"
                  ^^ !^"[" ^^ !^(Nat_big_num.to_string n) ^^ !^"]"
    in
    Dnode (pp_array nopt, [dtree_of_ctype cty])
  | Function (has_proto, (qs, cty), args, is_var) ->
    Dnode (pp_ctor "Function", filter_opt_list
           [ guarded_opt is_var (Dleaf (pp_keyword "variadic"))
           ; Some (Dnode (pp_ctor "Arguments", List.map dtree_of_argument args))
           ; Some (dtree_of_ctype cty)
           ; guarded_opt (qs.const || qs.restrict || qs.volatile)
               (Dleaf (pp_qualifiers qs))
           ; guarded_opt has_proto (Dleaf (pp_keyword "has_prototype"))
           ])
  | Pointer (qs, cty) ->
    Dnode (pp_ctor "Pointer", filter_opt_list
           [ guarded_opt (qs.const || qs.restrict || qs.volatile)
               (Dleaf (pp_qualifiers qs))
           ; Some (dtree_of_ctype cty)])
  | Atomic cty ->
    Dnode (pp_ctor "Atomic", [dtree_of_ctype cty])
  | Struct i ->
    Dleaf (pp_type_keyword "struct" ^^^ pp_id i)
  | Union i ->
    Dleaf (pp_type_keyword "union" ^^^ pp_id i)
  | Builtin s ->
    Dleaf (pp_ctor "Builtin" ^^^ !^s)

and dtree_of_argument (qs, cty, is_register) =
  if qs.const || qs.restrict || qs.volatile || is_register then
    Dnode (pp_qualifiers qs ^^ (if is_register then P.space ^^ pp_keyword "register" else P.empty),
           [dtree_of_ctype cty])
  else dtree_of_ctype cty

let dtree_of_expression pp_annot expr =
  let rec self (AnnotatedExpression (annot, _, loc, expr_)) =
    let pp_stmt_ctor str =
      pp_stmt_ctor str ^^^ pp_annot annot in
    let pp_cabs_id = Pp_cabs.pp_cabs_identifier in
    let dtree_of_generic_association = function
      | AilGAtype (ty, e) ->
        Dnode ( pp_stmt_ctor "AilGAtype", [ dtree_of_ctype ty; self e ] )
      | AilGAdefault e ->
        Dnode ( pp_stmt_ctor "AilGAdefault", [ self e] )
    in
    let dtree_of_field (cid, e_opt) =
      match e_opt with
      | Some e -> Dnode (pp_cabs_id cid, [self e])
      | None   -> Dleaf (pp_cabs_id cid)
    in
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
          Dnode ( pp_stmt_ctor "AilEcast"
                , [dtree_of_ctype ty; self e] )
      | AilEcall (e, es) ->
          Dnode ( pp_stmt_ctor "AilEcall"
                , (self e) :: (List.map self es) )
      | AilEassert e ->
          Dnode ( pp_stmt_ctor "AilEassert"
                , [self e] )
      | AilEoffsetof (ty, ident) ->
          Dnode ( pp_stmt_ctor "AilEoffsetof" ^^^ pp_cabs_id ident
                , [dtree_of_ctype ty] )
      | AilEgeneric (e, gas) ->
          Dnode ( pp_stmt_ctor "AilEgeneric"
                , (self e) :: List.map dtree_of_generic_association gas )
      | AilEarray (ty, e_opts) ->
          Dnode ( pp_stmt_ctor "AilEarray"
                , filter_opt_list (Some (dtree_of_ctype ty) :: List.map (option None self) e_opts) )
      | AilEstruct (tag_sym, xs) ->
          Dnode ( pp_stmt_ctor "AilEstruct" ^^^ pp_id tag_sym
                , List.map dtree_of_field xs )
      | AilEunion (tag_sym, memb_ident, e_opt) ->
          Dnode ( pp_stmt_ctor "AilEunion" ^^^ pp_id tag_sym
                , [dtree_of_field (memb_ident, e_opt)] )
      | AilEcompound (ty, e) ->
          Dnode ( pp_stmt_ctor "AilEcompound"
                , [dtree_of_ctype ty; self e] )
      | AilEmemberof (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberof" ^^^ pp_cabs_id ident
                , [self e] )
      | AilEmemberofptr (e, ident) ->
          Dnode ( pp_stmt_ctor "AilEmemberofptr" ^^^ pp_cabs_id ident
                , [self e] )
      | AilEbuiltin str ->
          Dleaf ( pp_stmt_ctor "AilEbuiltin" ^^^ !^str )
      | AilEstr lit ->
          Dleaf ( pp_stmt_ctor "AilEstr" ^^^ pp_stringLiteral lit )
      | AilEconst c ->
          Dleaf ( pp_stmt_ctor "AilEconst" ^^^ pp_constant c )
      | AilEident sym ->
          Dleaf ( pp_stmt_ctor "AilEident" ^^^ pp_symbol sym )
      | AilEsizeof (qs, ty) ->
          Dnode ( pp_stmt_ctor "AilEsizeof", [dtree_of_argument (qs, ty, false)] )
      | AilEsizeof_expr e ->
          Dnode ( pp_stmt_ctor "AilEsizeof_expr", [self e] )
      | AilEalignof (qs, ty) ->
          Dnode ( pp_stmt_ctor "AilEalignof", [dtree_of_argument (qs, ty, false)] )
      | AilEannot (ty, e) ->
          Dnode ( pp_stmt_ctor "AilEannot", [dtree_of_ctype ty; self e] )
      | AilEva_start (e, sym) ->
          Dnode ( pp_stmt_ctor "AilEva_start" ^^^ pp_id sym
                , [self e] )
      | AilEva_arg (e, ty) ->
          Dnode ( pp_stmt_ctor "AilEva_arg", [dtree_of_ctype ty; self e] )
      | AilEprint_type e ->
          Dnode ( pp_stmt_ctor "AilEprint_type", [self e])
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
        Dnode ( pp_stmt_ctor "AilScase" ^^^ pp_integerConstant iCst
              , [dtree_of_statement s] )
    | AilSdefault s ->
        Dnode ( pp_stmt_ctor "AilSdefault"
              , [dtree_of_statement s] )
    | AilSlabel (sym, s) ->
        Dnode ( pp_stmt_ctor "AilSlabel" ^^^ pp_id sym
              , [dtree_of_statement s] )
    | AilSgoto sym ->
        Dleaf ( pp_stmt_ctor "AilSgoto" ^^^ pp_id sym )
    | AilSdeclaration xs ->
        Dnode ( pp_stmt_ctor "AilSdeclaration"
              , List.map (fun (sym, e) ->
                  Dnode (pp_stmt_ctor "Symbol" ^^^ pp_id sym, [dtree_of_expression e])
                ) xs )
    | AilSpar ss ->
        failwith "NON-STD cppmem threads"

let dtree_of_function_definition pp_annot (fun_sym, (param_syms, stmt)) =
  let param_dtrees =
    [] in
  Dnode ( pp_id fun_sym
        , param_dtrees @ [dtree_of_statement pp_annot stmt] )

let dtree_of_declaration (i, decl) =
  let pp_maybe_storage = function
    | Some (sd, b) -> pp_storageDuration sd (*TODO: what is this bool? *)
    | None -> pp_keyword "register"
  in
  match decl with
  | Decl_object (msd, qs, cty) ->
    Dnode (pp_ctor "Decl_object" ^^^ pp_id i, filter_opt_list
           [ Some (dtree_of_ctype cty)
           ; Some (Dleaf (pp_maybe_storage msd))
           ; guarded_opt (qs.const || qs.restrict || qs.volatile)
               (Dleaf (pp_qualifiers qs))])
  | Decl_function (has_proto, (qs, cty), args, is_var, is_inline, is_noreturn) ->
    Dnode (pp_ctor "Decl_function" ^^^ pp_id i, filter_opt_list
           [ guarded_opt is_noreturn (Dleaf (pp_keyword "Noreturn"))
           ; guarded_opt is_inline (Dleaf (pp_keyword "inline"))
           ; guarded_opt is_var (Dleaf (pp_keyword "variadic"))
           ; Some (Dnode (pp_ctor "Arguments", List.map dtree_of_argument args))
           ; Some (dtree_of_ctype cty)
           ; guarded_opt (qs.const || qs.restrict || qs.volatile)
               (Dleaf (pp_qualifiers qs))
           ; guarded_opt has_proto (Dleaf (pp_keyword "has_prototype"))
           ])

let dtree_of_program pp_annot (_, sigm) =
  Dnode ( pp_ctor "AilSigma" ,
          [ Dnode (pp_ctor "AilDeclarations"
                  , List.map dtree_of_declaration sigm.declarations)
          ; Dnode (pp_ctor "AilTagDefinitions", [])
          ; Dnode (pp_ctor "AilObjectDeclarations", [])
          ; Dnode ( pp_ctor "AilFunctionDefinitions"
                  , List.map (dtree_of_function_definition pp_annot)
                      sigm.function_definitions )
          ; Dnode (pp_ctor "AilStaticAssertions", [])
          ] )

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
  pp_doc_tree (dtree_of_program (fun _ -> P.empty) p)

(* For debugging: prints all the type annotations *)
let pp_program_with_annot (p: GenTypes.genTypeCategory program) : PPrint.document =
  pp_doc_tree (dtree_of_program pp_annot p)
