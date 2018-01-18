open Cabs

open Pp_prelude
open Pp_ast
open Colour

module P = PPrint

let precedence = function
  | CabsEident _
  | CabsEconst _
  | CabsEstring _
  | CabsEgeneric _
  | CabsEsubscript _
  | CabsEcall _
  | CabsEmemberof _
  | CabsEmemberofptr _
  | CabsEpostincr _
  | CabsEpostdecr _
  | CabsEpreincr _
  | CabsEpredecr _
  | CabsEassert _
  | CabsEoffsetof _
  | CabsEva_start _
  | CabsEva_arg _
  | CabsEcompound _
  | CabsEprint_type _ -> Some 1
  | CabsEunary _
  | CabsEsizeof_expr _
  | CabsEsizeof_type _
  | CabsEalignof _
  | CabsEcast _ -> Some 2
  | CabsEbinary (CabsMul, _, _)
  | CabsEbinary (CabsDiv, _, _)
  | CabsEbinary (CabsMod, _, _) -> Some 3
  | CabsEbinary (CabsAdd, _, _)
  | CabsEbinary (CabsSub, _, _) -> Some 4
  | CabsEbinary (CabsShl, _, _)
  | CabsEbinary (CabsShr, _, _) -> Some 5
  | CabsEbinary (CabsLt, _, _)
  | CabsEbinary (CabsGt, _, _)
  | CabsEbinary (CabsLe, _, _)
  | CabsEbinary (CabsGe, _, _) -> Some 6
  | CabsEbinary (CabsEq, _, _)
  | CabsEbinary (CabsNe, _, _) -> Some 7
  | CabsEbinary (CabsBand, _, _) -> Some 8
  | CabsEbinary (CabsBxor, _, _) -> Some 9
  | CabsEbinary (CabsBor, _, _) -> Some 10
  | CabsEbinary (CabsAnd, _, _) -> Some 11
  | CabsEbinary (CabsOr, _, _) -> Some 12
  | CabsEcond _ -> Some 13
  | CabsEassign _ -> Some 14
  | CabsEcomma _ -> Some 15

let lt_precedence p1 p2 =
  match p1, p2 with
    | Some n1, Some n2 -> n1 < n2
    | Some _ , None    -> true
    | None   , _       -> false

let pp_colour_keyword k =
  !^(ansi_format [Bold; Cyan] k)

let pp_colour_type_keyword k =
  !^(ansi_format [Green] k)

let pp_colour_identifier id =
  !^(ansi_format [Yellow] id)

let pp_colour_function_identifier id =
  !^(ansi_format [Bold; Blue] id)

let pp_colour_label (CabsIdentifier (_, str)) =
  !^(ansi_format [Magenta] str)

let pp_decl_ctor k =
  !^ (ansi_format [Bold; Green] k)


let pp_location = function
  | Location_ocaml.Loc_unknown ->
      P.angles (!^ "unknown location")
  | Location_ocaml.Loc_point pos ->
      Lexing.(
        let line = string_of_int pos.pos_lnum in
        let col  = string_of_int (1+pos.pos_cnum - pos.pos_bol) in
        P.angles !^ (ansi_format [Yellow] ("line:" ^ line ^ ":" ^ col))
      )
  | Location_ocaml.Loc_region (start_p, end_p, cursor_p_opt) ->
      Lexing. (
        let start_line = string_of_int start_p.pos_lnum in
        let start_col  = string_of_int (1+start_p.pos_cnum - start_p.pos_bol) in
        let end_line   = string_of_int end_p.pos_lnum in
        let end_col    = string_of_int (1+end_p.pos_cnum - end_p.pos_bol) in
        P.angles (
          if start_p.pos_lnum = end_p.pos_lnum then
            !^ (ansi_format [Yellow] ("line:" ^ start_line ^ ":" ^ start_col))
            ^^ P.comma ^^^
            !^ (ansi_format [Yellow] ("col:" ^ end_col))
          else
            !^ (ansi_format [Yellow] ("line:" ^ start_line ^ ":" ^ start_col))
            ^^ P.comma ^^^
            !^ (ansi_format [Yellow] ("line:" ^ end_line ^ ":" ^ end_col))
        ) ^^ P.optional (fun p ->
               let line = string_of_int p.pos_lnum in
               let col  = string_of_int (1+p.pos_cnum - p.pos_bol) in
               P.space ^^
               !^ (ansi_format [Yellow] (
               if start_p.pos_lnum = end_p.pos_lnum then
                 "col:" ^ col
               else
                 "line:" ^ line ^ ":" ^ col))
             ) cursor_p_opt
      )

let map_option f = function
  | Some x -> Some (f x)
  | None   -> None

let pp_option pp = function
  | Some z ->
      !^ "Some" ^^ P.brackets (pp z)
  | None ->
      !^ "None"

let dtree_of_pair dtree_of1 dtree_of2 (x, y) =
  Dnode (pp_ctor "Pair", [dtree_of1 x; dtree_of2 y])

let dtree_of_list dtree_of = function
  | [] ->
      Dleaf (pp_ctor "EmptyList")
  | xs ->
      Dnode (pp_ctor "List", List.map dtree_of xs)

let leaf_of_option pp = function
  | Some z ->
      Dleaf (pp_ctor "Some" ^^ P.brackets (pp z))
  | None ->
      Dleaf (pp_ctor "None")

let node_of_option dtree_of = function
  | Some z ->
      Dnode (pp_ctor "Some", [dtree_of z])
  | None ->
      Dleaf (pp_ctor "None")

let node_of_list_option dtree_of = function
  | Some xs ->
      List.map dtree_of xs
  | None ->
      [ Dleaf (pp_ctor "None") ]

let pp_cabs_identifier (CabsIdentifier (loc, str)) =
  pp_location loc ^^^ pp_colour_identifier str

let pp_bool = function
  | true  -> !^ "true"
  | false -> !^ "false"

let pp_cabs_integer_suffix = function
  | CabsSuffix_U   -> !^ "u"
  | CabsSuffix_UL  -> !^ "ul"
  | CabsSuffix_ULL -> !^ "ull"
  | CabsSuffix_L   -> !^ "l"
  | CabsSuffix_LL  -> !^ "ll"

let pp_cabs_integer_constant (str, suff_opt) =
  !^ str ^^ P.optional pp_cabs_integer_suffix suff_opt

let pp_cabs_character_prefix = function
  | CabsPrefix_L -> !^ "L"
  | CabsPrefix_u -> !^ "u"
  | CabsPrefix_U -> !^ "U"

let pp_cabs_character_constant (pref_opt, str) =
  P.optional pp_cabs_character_prefix pref_opt ^^ P.squotes (!^ str)

let pp_cabs_constant = function
  | CabsInteger_const icst ->
      pp_stmt_ctor "CabsInteger_const" ^^^ pp_cabs_integer_constant icst
  | CabsFloating_const str ->
      pp_stmt_ctor "CabsFloating_const" ^^^ !^ str
  | CabsEnumeration_const ->
      pp_stmt_ctor "CabsEnumeration_const"
  | CabsCharacter_const ccst ->
      pp_stmt_ctor "CabsCharacter_const" ^^^ pp_cabs_character_constant ccst


let pp_cabs_encoding_prefix = function
  | CabsEncPrefix_u8 -> !^ "u8"
  | CabsEncPrefix_u  -> !^ "u"
  | CabsEncPrefix_U  -> !^ "U"
  | CabsEncPrefix_L  -> !^ "L"

let pp_cabs_string_literal (pref_opt, strs) =
  P.optional pp_cabs_encoding_prefix pref_opt ^^ P.dquotes (!^ (String.concat "" strs))

let rec dtree_of_cabs_expression (CabsExpression (loc, expr)) =
  match expr with
    | CabsEident ident ->
        Dleaf (pp_stmt_ctor "CabsEident" ^^^ pp_location loc ^^^ pp_cabs_identifier ident)
    | CabsEconst cst ->
        Dleaf (pp_stmt_ctor "CabsEconst" ^^^ pp_location loc ^^^ pp_cabs_constant cst)
    | CabsEstring lit ->
        Dleaf (pp_stmt_ctor "CabsEstring" ^^^ pp_location loc ^^^ pp_cabs_string_literal lit)
    | CabsEgeneric (e, gs) ->
        Dnode ( pp_stmt_ctor "CabsEgeneric" ^^^ pp_location loc
              , [dtree_of_cabs_expression e; dtree_of_list dtree_of_cabs_generic_association gs] )
    | CabsEsubscript (e1, e2) ->
        Dnode ( pp_stmt_ctor "CabsEsubscript" ^^^ pp_location loc
              , [dtree_of_cabs_expression e1; dtree_of_cabs_expression e2] )
    | CabsEcall (e, es) ->
        Dnode ( pp_stmt_ctor "CabsEcall" ^^^ pp_location loc
              , [dtree_of_cabs_expression e; dtree_of_list dtree_of_cabs_expression es] )
    | CabsEassert e ->
        Dnode (pp_stmt_ctor "CabsEassert" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEoffsetof (tyname, ident) ->
        Dnode ( pp_stmt_ctor "CabsEoffsetof" ^^^ pp_location loc ^^^ pp_cabs_identifier ident
              , [dtree_of_type_name tyname] )
    | CabsEmemberof (e, ident) ->
        Dnode ( pp_stmt_ctor "CabsEmemberof" ^^^ pp_location loc ^^^ P.dot ^^ pp_cabs_identifier ident
              , [dtree_of_cabs_expression e] )
    | CabsEmemberofptr (e, ident) ->
        Dnode ( pp_stmt_ctor "CabsEmemberofptr" ^^^ pp_location loc ^^^ P.dot ^^ pp_cabs_identifier ident
              , [dtree_of_cabs_expression e] )
    | CabsEpostincr e ->
        Dnode (pp_stmt_ctor "CabsEpostincr" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEpostdecr e ->
        Dnode (pp_stmt_ctor "CabsEpostdecr" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEcompound (tyname, inits) ->
        Dnode ( pp_stmt_ctor "CabsEcompound" ^^^ pp_location loc
              , [dtree_of_type_name tyname; dtree_of_initializer_list inits] )
    | CabsEpreincr e ->
        Dnode (pp_stmt_ctor "CabsEpreincr" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEpredecr e ->
        Dnode (pp_stmt_ctor "CabsEpredecr" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEunary (uop, e) ->
        Dnode (pp_stmt_ctor "CabsEunary" ^^^ pp_location loc ^^^ pp_cabs_unary_operator uop, [dtree_of_cabs_expression e])
    | CabsEsizeof_expr e ->
        Dnode (pp_stmt_ctor "CabsEsizeof_expr" ^^^ pp_location loc, [dtree_of_cabs_expression e])
    | CabsEsizeof_type tyname ->
        Dnode (pp_stmt_ctor "CabsEsizeof_type" ^^^ pp_location loc, [dtree_of_type_name tyname])
    | CabsEalignof tyname ->
        Dnode (pp_stmt_ctor "CabsEalignof" ^^^ pp_location loc, [dtree_of_type_name tyname])
    | CabsEcast (tyname, e) ->
        Dnode (pp_stmt_ctor "CabsEcast" ^^^ pp_location loc, [dtree_of_type_name tyname; dtree_of_cabs_expression e] )
    | CabsEbinary (bop, e1, e2) ->
        Dnode ( pp_stmt_ctor "CabsEbinary" ^^^ pp_location loc ^^^ pp_cabs_binary_operator bop
              , [dtree_of_cabs_expression e1; dtree_of_cabs_expression e2] )
    | CabsEcond (e1, e2, e3) ->
        Dnode ( pp_stmt_ctor "CabsEcond" ^^^ pp_location loc
              , [dtree_of_cabs_expression e1; dtree_of_cabs_expression e2; dtree_of_cabs_expression e3] )
    | CabsEassign (aop, e1, e2) ->
        Dnode ( pp_stmt_ctor "CabsEassign" ^^^ pp_location loc ^^^ pp_cabs_assignment_operator aop
              , [dtree_of_cabs_expression e1; dtree_of_cabs_expression e2] )
    | CabsEcomma (e1, e2) ->
        Dnode ( pp_stmt_ctor "CabsEcomma" ^^^ pp_location loc
              , [dtree_of_cabs_expression e1; dtree_of_cabs_expression e2] )
    | CabsEva_start (e, ident) ->
        Dnode ( pp_stmt_ctor "CabsEva_start" ^^^ pp_location loc ^^^ pp_cabs_identifier ident
              , [dtree_of_cabs_expression e] )
    | CabsEva_arg (e, tyname) ->
        Dnode (pp_stmt_ctor "CabsEva_arg" ^^^ pp_location loc, [dtree_of_cabs_expression e; dtree_of_type_name tyname] )
    | CabsEprint_type e ->
        Dnode (pp_stmt_ctor "CabsEprint_type" ^^^ pp_location loc, [dtree_of_cabs_expression e])

and dtree_of_cabs_generic_association = function
  | GA_type (tyname, e) ->
      Dnode ( pp_ctor "GA_type"
            , [ dtree_of_type_name tyname
              ; dtree_of_cabs_expression e] )
  | GA_default e ->
      Dnode (pp_ctor "GA_default", [dtree_of_cabs_expression e])

and pp_cabs_unary_operator = function
  | CabsAddress ->
      !^ "&"
  | CabsIndirection ->
      !^ "*"
  | CabsPlus ->
      !^ "+"
  | CabsMinus ->
      !^ "-"
  | CabsBnot ->
      !^ "~"
  | CabsNot ->
      !^ "!"

and pp_cabs_binary_operator = function
  | CabsMul ->
      !^ "*"
  | CabsDiv ->
      !^ "/"
  | CabsMod ->
      !^ "%"
  | CabsAdd ->
      !^ "+"
  | CabsSub ->
      !^ "-"
  | CabsShl ->
      !^ "<<"
  | CabsShr ->
      !^ ">>"
  | CabsLt ->
      !^ "<"
  | CabsGt ->
      !^ ">"
  | CabsLe ->
      !^ "<="
  | CabsGe ->
      !^ ">="
  | CabsEq ->
      !^ "=="
  | CabsNe ->
      !^ "!="
  | CabsBand ->
      !^ "&"
  | CabsBxor ->
      !^ "^"
  | CabsBor ->
      !^ "|"
  | CabsAnd ->
      !^ "&&"
  | CabsOr ->
      !^ "||"

and pp_cabs_assignment_operator = function
  | Assign ->
      !^ "="
  | Assign_Mul ->
      !^ "*="
  | Assign_Div ->
      !^ "/="
  | Assign_Mod ->
      !^ "%="
  | Assign_Add ->
      !^ "+="
  | Assign_Sub ->
      !^ "-="
  | Assign_Shl ->
      !^ "<<="
  | Assign_Shr ->
      !^ ">>="
  | Assign_Band ->
      !^ "&="
  | Assign_Bxor ->
      !^ "^="
  | Assign_Bor ->
      !^ "|="

and dtree_of_declaration = function
  | Declaration_base (specifs, []) ->
      Dnode (pp_decl_ctor "Declaration_base", [dtree_of_specifiers specifs])
  | Declaration_base (specifs, idecls) ->
      Dnode ( pp_decl_ctor "Declaration_base"
            , (dtree_of_specifiers specifs) :: List.map dtree_of_init_declarator idecls )
  | Declaration_static_assert sa_decl ->
      Dnode ( pp_decl_ctor "Declaration_static_assert"
            , [dtree_of_static_assert_declaration sa_decl] )

and dtree_of_specifiers specifs =
  Dnode (pp_ctor "Specifiers", filter_opt_list [
      leaf_opt_list "Storage_class_specifiers" pp_storage_class_specifier   specifs.storage_classes     ;
      node_opt_list "Type_specifiers"          dtree_of_cabs_type_specifier specifs.type_specifiers     ;
      leaf_opt_list "Type_qualifiers"          pp_cabs_type_qualifier       specifs.type_qualifiers     ;
      leaf_opt_list "Function_specifiers"      pp_function_specifier        specifs.function_specifiers ;
      node_opt_list "Alignment_specifiers"     dtree_of_alignment_specifier specifs.alignment_specifiers;
  ])

and dtree_of_init_declarator = function
  | InitDecl (_, decltor, init_opt) ->
      Dnode ( pp_decl_ctor "InitDecl"
            , [ dtree_of_declarator decltor; node_of_option dtree_of_initializer_ init_opt ] )

and pp_storage_class_specifier = function
  | SC_typedef ->
      pp_ctor "SC_typedef"
  | SC_extern ->
      pp_ctor "SC_extern"
  | SC_static ->
      pp_ctor "SC_static"
  | SC_Thread_local ->
      pp_ctor "SC_Thread_local"
  | SC_auto ->
      pp_ctor "SC_auto"
  | SC_register ->
      pp_ctor "SC_register"

and dtree_of_cabs_type_specifier = function
  | TSpec_void ->
      Dleaf (pp_ctor "TSpec_void")
  | TSpec_char ->
      Dleaf (pp_ctor "TSpec_char")
  | TSpec_short ->
      Dleaf (pp_ctor "TSpec_short")
  | TSpec_int ->
      Dleaf (pp_ctor "TSpec_int")
  | TSpec_long ->
      Dleaf (pp_ctor "TSpec_long")
  | TSpec_float ->
      Dleaf (pp_ctor "TSpec_float")
  | TSpec_double ->
      Dleaf (pp_ctor "TSpec_double")
  | TSpec_signed ->
      Dleaf (pp_ctor "TSpec_signed")
  | TSpec_unsigned ->
      Dleaf (pp_ctor "TSpec_unsigned")
  | TSpec_Bool ->
      Dleaf (pp_ctor "TSpec__Bool")
  | TSpec_Complex ->
      Dleaf (pp_ctor "TSpec__Complex")
  | TSpec_Atomic tyname ->
      Dnode (pp_ctor "TSpec_Atomic", [dtree_of_type_name tyname])
  | TSpec_struct (id_opt, s_decls_opt) ->
      Dnode (pp_ctor "TSpec_struct" ^^ P.brackets (pp_option pp_cabs_identifier id_opt),
               node_of_list_option dtree_of_struct_declaration s_decls_opt)
  | TSpec_union (id_opt, s_decls_opt) ->
      Dnode (pp_ctor "TSpec_union" ^^ P.brackets (pp_option pp_cabs_identifier id_opt),
               node_of_list_option dtree_of_struct_declaration s_decls_opt)
  | TSpec_enum (id_opt, enums_opt) ->
      Dnode (pp_ctor "TSpec_enum" ^^ P.brackets (pp_option pp_cabs_identifier id_opt),
             node_of_list_option dtree_of_enumerator enums_opt)
  | TSpec_name id ->
      Dleaf (pp_ctor "TSpec_name" ^^ P.brackets (pp_cabs_identifier id))

and dtree_of_struct_declaration = function
  | Struct_declaration (specs, qs, s_decls) ->
      Dnode (pp_ctor "Struct_declaration", filter_opt_list [
        node_opt_list "Type_specifiers"   dtree_of_cabs_type_specifier specs  ;
        leaf_opt_list "Type_qualifiers"   pp_cabs_type_qualifier       qs     ;
        node_opt_list "Struct_declarator" dtree_of_struct_declarator   s_decls ])
  | Struct_assert sa_decl ->
      Dnode (pp_ctor "Struct_assert", [dtree_of_static_assert_declaration sa_decl])

and dtree_of_struct_declarator = function
  | SDecl_simple decltor ->
      Dnode (pp_ctor "SDecl_simple", [dtree_of_declarator decltor])
  | SDecl_bitfield (decltor_opt, e) ->
      Dnode (pp_ctor "SDecl_bitfield", filter_opt_list [
          map_option dtree_of_declarator decltor_opt;
          Some (dtree_of_cabs_expression e) ])

and dtree_of_static_assert_declaration = function
  | Static_assert (e, s) -> Dnode (pp_decl_ctor "Static_assert", [
      dtree_of_cabs_expression e;
      Dleaf (pp_cabs_string_literal s)])

and dtree_of_enumerator (id, e_opt) =
  Dnode (pp_cabs_identifier id ^^^ P.comma, [node_of_option dtree_of_cabs_expression e_opt])

and pp_cabs_type_qualifier = function
  | Q_const ->
      pp_ctor "Q_const"
  | Q_restrict ->
      pp_ctor "Q_restrict"
  | Q_volatile ->
      pp_ctor "Q_volatile"
  | Q_Atomic ->
      pp_ctor "Q_Atomic"

and pp_function_specifier = function
  | FS_inline ->
      pp_ctor "FS_inline"
  | FS_Noreturn ->
      pp_ctor "FS_Noreturn"

and dtree_of_alignment_specifier = function
  | AS_type tyname ->
      Dnode (pp_ctor "AS_type", [dtree_of_type_name tyname])
  | AS_expr e ->
      Dnode (pp_ctor "AS_expr", [dtree_of_cabs_expression e])

and dtree_of_declarator = function
  | Declarator (ptr_decl_opt, ddecl) ->
      Dnode ( pp_decl_ctor "Declarator"
            , [ node_of_option dtree_of_pointer_declarator ptr_decl_opt
              ; dtree_of_direct_declarator ddecl ] )

and dtree_of_direct_declarator = function
  | DDecl_identifier ident ->
      Dleaf (pp_decl_ctor "DDecl_identifier" ^^^ pp_cabs_identifier ident)
  | DDecl_declarator decltor ->
      Dnode (pp_decl_ctor "DDecl_declarator", [dtree_of_declarator decltor])
  | DDecl_array (ddecltor, adecltor) ->
      Dnode ( pp_decl_ctor "DDecl_array"
            , [ dtree_of_direct_declarator ddecltor
              ; dtree_of_array_declarator adecltor ] )
  | DDecl_function (ddecltor, param_tys) ->
      Dnode ( pp_decl_ctor "DDecl_function"
            , [dtree_of_direct_declarator ddecltor; dtree_of_parameter_type_list param_tys] )

and dtree_of_array_declarator = function
  | ADecl (_, qs, is_static, a_decltor_size_opt) ->
      Dnode ( pp_decl_ctor "ADecl" ^^^ P.brackets (comma_list pp_cabs_type_qualifier qs) ^^
              (if is_static then P.space ^^ !^ "static" else P.empty)
            , [node_of_option dtree_of_array_declarator_size a_decltor_size_opt] )

and dtree_of_array_declarator_size = function
  | ADeclSize_expression e ->
      Dnode (pp_decl_ctor "ADEclSize_expression", [dtree_of_cabs_expression e])
  | ADeclSize_asterisk ->
      Dleaf (pp_decl_ctor "ADeclSize_asterisk")

and dtree_of_pointer_declarator = function
  | PDecl (qs, None) ->
      Dleaf (pp_decl_ctor "PDecl" ^^^ P.brackets (comma_list pp_cabs_type_qualifier qs))
  | PDecl (qs, Some ptr_decltor) ->
      Dnode ( pp_decl_ctor "PDecl" ^^^ P.brackets (comma_list pp_cabs_type_qualifier qs)
            , [dtree_of_pointer_declarator ptr_decltor] )

and dtree_of_parameter_type_list = function
  | Params ([], is_variadic) ->
      Dleaf (pp_decl_ctor "Params" ^^ (if is_variadic then P.space ^^ !^ "variadic" else P.empty) ^^^ !^ "empty")
  | Params (param_decls, is_variadic) ->
      Dnode ( pp_decl_ctor "Params" ^^ (if is_variadic then P.space ^^ !^ "variadic" else P.empty)
            , List.map dtree_of_parameter_declaration param_decls )

and dtree_of_parameter_declaration = function
  | PDeclaration_decl (specifs, decltor) ->
      Dnode ( pp_decl_ctor "PDeclaration_decl"
            , [dtree_of_specifiers specifs; dtree_of_declarator decltor] )
  | PDeclaration_abs_decl (specifs, None) ->
      Dnode (pp_ctor "PDeclaration_abs_decl", [dtree_of_specifiers specifs])
  | PDeclaration_abs_decl (specifs, Some abs_decltor) ->
      Dnode ( pp_ctor "PDeclaration_abs_decl"
              , [dtree_of_specifiers specifs; dtree_of_abstract_declarator abs_decltor] )

and dtree_of_type_name = function
  | Type_name (specs, qs, None) ->
      Dnode ( pp_decl_ctor "Type_name", filter_opt_list [
        node_opt_list "Type_specifiers" dtree_of_cabs_type_specifier specs;
        leaf_opt_list "Type_qualifiers" pp_cabs_type_qualifier       qs   ] )
  | Type_name (specs, qs, Some a_decltor) ->
      Dnode ( pp_decl_ctor "Type_name", filter_opt_list [
        node_opt_list "Type_specifiers" dtree_of_cabs_type_specifier specs;
        leaf_opt_list "Type_qualifiers" pp_cabs_type_qualifier       qs   ;
        Some (dtree_of_abstract_declarator a_decltor)] )

and dtree_of_abstract_declarator = function
  | AbsDecl_pointer ptr_decltor ->
      Dnode (pp_decl_ctor "AbsDecl_pointer", [dtree_of_pointer_declarator ptr_decltor])
  | AbsDecl_direct (ptr_decltor_opt, dabs_decltor) ->
      Dnode ( pp_decl_ctor "AbsDecl_direct"
            , [ node_of_option dtree_of_pointer_declarator ptr_decltor_opt
              ; dtree_of_direct_abstract_declarator dabs_decltor ] )

and dtree_of_direct_abstract_declarator = function
  | DAbs_abs_declarator abs_decltor ->
      Dnode ( pp_decl_ctor "DAbs_abs_declarator"
            , [dtree_of_abstract_declarator abs_decltor] )
  | DAbs_array (dabs_decltor_opt, abs_decltor) ->
      Dnode ( pp_decl_ctor "DAbs_array"
            , [ node_of_option dtree_of_direct_abstract_declarator dabs_decltor_opt
              ; dtree_of_array_declarator abs_decltor ] )
  | DAbs_function (dabs_decltor_opt, param_tys) ->
      Dnode ( pp_decl_ctor "DAbs_function"
            , node_of_option dtree_of_direct_abstract_declarator dabs_decltor_opt ::
              [dtree_of_parameter_type_list param_tys] )

and dtree_of_initializer_ = function
  | Init_expr e ->
      Dnode (pp_decl_ctor "Init_expr", [dtree_of_cabs_expression e])
  | Init_list inits ->
      Dnode (pp_decl_ctor "Init_list", [dtree_of_initializer_list inits])

and dtree_of_designator = function
  | Desig_array e ->
      Dnode (pp_decl_ctor "Desig_array", [dtree_of_cabs_expression e])
  | Desig_member ident ->
      Dleaf (pp_decl_ctor "Desig_member" ^^^ pp_cabs_identifier ident)

and dtree_of_initializer_list inits =
  dtree_of_list (fun (desigs_opt, init) ->
    match desigs_opt with
      | Some desigs ->
          dtree_of_pair
            (dtree_of_list dtree_of_designator)
            dtree_of_initializer_
            (desigs, init)
      | None ->
          dtree_of_initializer_ init
  ) inits


let rec dtree_of_cabs_statement (CabsStatement (loc, stmt_)) =
  match stmt_ with
  | CabsSlabel (ident, s) ->
      Dnode ( pp_stmt_ctor "CabsSlabel" ^^^ pp_colour_label ident
            , [dtree_of_cabs_statement s] )
  | CabsScase (e, s) ->
      Dnode ( pp_stmt_ctor "CabsScase"
            , [dtree_of_cabs_expression e; dtree_of_cabs_statement s] )
  | CabsSdefault s ->
      Dnode (pp_stmt_ctor "CabsSdefault", [dtree_of_cabs_statement s])
  | CabsSblock [] ->
      Dleaf (pp_stmt_ctor "CabsSblock" ^^^ !^ "empty")
  | CabsSblock ss ->
      Dnode (pp_stmt_ctor "CabsSblock", List.map dtree_of_cabs_statement ss)
  | CabsSdecl decl ->
      Dnode (pp_stmt_ctor "CabsSdecl", [dtree_of_declaration decl])
  | CabsSnull ->
      Dleaf (pp_stmt_ctor "CabsSnull")
  | CabsSexpr e ->
      Dnode (pp_stmt_ctor "CabsSexpr", [dtree_of_cabs_expression e])
  | CabsSif (e, s1, s2_opt) ->
      Dnode ( pp_stmt_ctor "CabsSif"
            , [ dtree_of_cabs_expression e
              ; dtree_of_cabs_statement s1
              ; node_of_option dtree_of_cabs_statement s2_opt ] )
  | CabsSswitch (e, s) ->
      Dnode (pp_stmt_ctor "CabsSswitch", [dtree_of_cabs_expression e; dtree_of_cabs_statement s])
  | CabsSwhile (e, s) ->
      Dnode (pp_stmt_ctor "CabsSwhile", [dtree_of_cabs_expression e; dtree_of_cabs_statement s])
  | CabsSdo (e, s) ->
      Dnode (pp_stmt_ctor "CabsSdo", [dtree_of_cabs_expression e; dtree_of_cabs_statement s])
  | CabsSfor (fc_opt, e1_opt, e2_opt, s) ->
      Dnode ( pp_stmt_ctor "CabsSfor"
            , [ node_of_option dtree_of_for_clause fc_opt
              ; node_of_option dtree_of_cabs_expression e1_opt
              ; node_of_option dtree_of_cabs_expression e2_opt
              ; dtree_of_cabs_statement s ] )
  | CabsSgoto ident ->
      Dleaf (pp_stmt_ctor "CabsSgoto" ^^^ pp_colour_label ident)
  | CabsScontinue ->
      Dleaf (pp_stmt_ctor "CabsScontinue")
  | CabsSbreak ->
      Dleaf (pp_stmt_ctor "CabsSbreak")
  | CabsSreturn e_opt ->
      Dnode (pp_stmt_ctor "CabsSreturn", [node_of_option dtree_of_cabs_expression e_opt])
  | CabsSpar [] ->
      Dleaf (pp_stmt_ctor "CabsSpar" ^^^ !^ "empty")
  | CabsSpar ss ->
      Dnode (pp_stmt_ctor "CabsSpar", List.map dtree_of_cabs_statement ss)

and dtree_of_for_clause = function
 | FC_expr e ->
     Dnode (pp_stmt_ctor "FC_expr", [dtree_of_cabs_expression e])
 | FC_decl decl ->
     Dnode (pp_stmt_ctor "FC_decl", [dtree_of_declaration decl])


let dtree_of_function_definition (FunDef (_, specifs, decltor, stmt)) =
  Dnode ( pp_ctor "FunDef"
        , [ dtree_of_specifiers specifs
          ; dtree_of_declarator decltor
          ; dtree_of_cabs_statement stmt ] )


let dtree_of_external_declaration = function
  | EDecl_func fdef ->
      Dnode (pp_decl_ctor "EDecl_func", [dtree_of_function_definition fdef])
  | EDecl_decl decl ->
      Dnode (pp_decl_ctor "EDecl_decl", [dtree_of_declaration decl])

let filter_external_decl edecls =
  let f acc decl =
    match decl with
    | EDecl_func _ -> decl::acc
    | _ -> acc
  in List.rev (List.fold_left f [] edecls)

let pp_translation_unit show_ext_decl do_colour (TUnit edecls) =
  Colour.do_colour := do_colour && Unix.isatty Unix.stdout;
  let filtered_edecls = if show_ext_decl then edecls else filter_external_decl edecls in
  pp_doc_tree (Dnode (pp_decl_ctor "TUnit", List.map dtree_of_external_declaration filtered_edecls)) ^^ P.hardline
