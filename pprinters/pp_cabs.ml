open Global
open Cabs

open Colour

module P = PPrint

let isatty = ref false


(* TODO move to global *)
let ($) f x = f x
let (-|) f g x = f (g x)


let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f
let space_list f = P.separate_map P.space f


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
  | CabsEcompound _ -> Some 1
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
  !^ (if !isatty then ansi_format [Bold; Cyan] k else k)

let pp_colour_type_keyword k =
  !^ (if !isatty then ansi_format [Green] k else k)

let pp_colour_identifier id =
  !^ (if !isatty then ansi_format [Yellow] id else id)

let pp_colour_function_identifier id =
  !^ (if !isatty then ansi_format [Bold; Blue] id else id)

let pp_colour_label (CabsIdentifier (_, str)) =
  !^ (if !isatty then ansi_format [Magenta] str else str)


let pp_cabs_identifier (CabsIdentifier (_, str)) =
  pp_colour_identifier str


(*
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
      pp_cabs_integer_constant icst
  | CabsFloating_const str ->
      !^ str
  | CabsEnumeration_const ->
      !^ "WIP[enumeration-constant]"
  | CabsCharacter_const ccst ->
      pp_cabs_character_constant ccst


let pp_cabs_encoding_prefix = function
  | CabsEncPrefix_u8 -> !^ "u8"
  | CabsEncPrefix_u  -> !^ "u"
  | CabsEncPrefix_U  -> !^ "U"
  | CabsEncPrefix_L  -> !^ "L"

let pp_cabs_string_literal (pref_opt, str) =
  P.optional pp_cabs_encoding_prefix pref_opt ^^ P.dquotes (!^ str)


let rec pp_cabs_expression p expr =
  let p' = precedence expr in
  let f = P.group -| pp_cabs_expression p' in
  (if lt_precedence p' p then fun x -> x else P.parens) $
    match expr with
      | CabsEident id ->
          pp_cabs_identifier id
      | CabsEconst cst ->
          pp_cabs_constant cst
      | CabsEstring str ->
          pp_cabs_string_literal str
      | CabsEgeneric (e, gs) ->
          pp_colour_keyword "_Generic" ^^ P.parens (f e ^^ P.comma ^^^ comma_list pp_generic_association gs)
      | CabsEsubscript (e1, e2) ->
          f e1 ^^ P.brackets (f e2)
      | CabsEcall (e, es) ->
          f e ^^ P.parens (comma_list f es)
      | CabsEmemberof (e, id) ->
          f e ^^ P.dot ^^ pp_cabs_identifier id
      | CabsEmemberofptr (e, id) ->
          f e ^^ !^ "->" ^^ pp_cabs_identifier id
      | CabsEpostincr e ->
          f e ^^ !^ "++"
      | CabsEpostdecr e ->
          f e ^^ !^ "--"
      | CabsEcompound (tyname, inits) ->
          P.parens (pp_type_name tyname) ^^^ P.braces (pp_initializer_list inits)
      | CabsEpreincr e ->
          !^ "++" ^^  f e
      | CabsEpredecr e ->
          !^ "--" ^^  f e
      | CabsEunary (uop, e) ->
          pp_cabs_unary_operator uop ^^ f e
      | CabsEsizeof_expr e ->
          pp_colour_keyword "sizeof"  ^^^ f e
      | CabsEsizeof_type tyname ->
          pp_colour_keyword "sizeof"  ^^ P.parens (pp_type_name tyname)
      | CabsEalignof tyname ->
          pp_colour_keyword "_Alignof" ^^ P.parens (pp_type_name tyname)
      | CabsEcast (tyname, e) ->
          P.parens (pp_type_name tyname) ^^^ f e
      | CabsEbinary (bop, e1, e2) ->
          f e1 ^^^ pp_cabs_binary_operator bop ^^^ f e2
      | CabsEcond (e1, e2, e3) ->
          P.group (f e1 ^^^ P.qmark ^/^ f e2 ^^^ P.colon ^/^ f e3)
      | CabsEassign (aop, e1, e2) ->
          f e1 ^^^ pp_cabs_assignment_operator aop ^^^ f e2
      | CabsEcomma (e1, e2) ->
          f e1 ^^ P.comma ^^^ f e2

and pp_generic_association = function
  | GA_type (tyname, e) ->
      pp_type_name tyname ^^ P.colon ^^^ pp_cabs_expression None e
  | GA_default e ->
      pp_colour_keyword "default" ^^ P.colon ^^^ pp_cabs_expression None e


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


and pp_declaration = function
  | Declaration_base (specifs, idecls) ->
      pp_specifiers specifs ^^ comma_list pp_init_declarator idecls ^^ P.semi
  | Declaration_static_assert sa_decl ->
      pp_static_assert_declaration sa_decl

and pp_specifiers specifs =
(*
  let zs = List.map pp_storage_class_specifier specifs.storage_classes      @
           List.map pp_cabs_type_specifier     specifs.type_specifiers      @
           List.map pp_cabs_type_qualifier     specifs.type_qualifiers      @
           List.map pp_function_specifier      specifs.function_specifiers  @
           List.map pp_alignment_specifier     specifs.alignment_specifiers in
*)
  space_list pp_storage_class_specifier specifs.storage_classes      ^^ (if specifs.storage_classes      = [] then P.empty else P.space) ^^
  space_list pp_cabs_type_specifier     specifs.type_specifiers      ^^ (if specifs.type_specifiers      = [] then P.empty else P.space) ^^
  space_list pp_cabs_type_qualifier     specifs.type_qualifiers      ^^ (if specifs.type_qualifiers      = [] then P.empty else P.space) ^^
  space_list pp_function_specifier      specifs.function_specifiers  ^^ (if specifs.function_specifiers  = [] then P.empty else P.space) ^^
  space_list pp_alignment_specifier     specifs.alignment_specifiers ^^ (if specifs.alignment_specifiers = [] then P.empty else P.space)

and pp_init_declarator = function
  | InitDecl (decltor, None) ->
      pp_declarator decltor
  | InitDecl (decltor, Some init) ->
      pp_declarator decltor ^^^ P.equals ^^^ pp_initializer_ init


and pp_storage_class_specifier = function
  | SC_typedef ->
      pp_colour_keyword "typedef"
  | SC_extern ->
      pp_colour_keyword "extern"
  | SC_static ->
      pp_colour_keyword "static"
  | SC_Thread_local ->
      pp_colour_keyword "_Thread_local"
  | SC_auto ->
      pp_colour_keyword "auto"
  | SC_register ->
      pp_colour_keyword "register"


and pp_cabs_type_specifier = function
  | TSpec_void ->
      pp_colour_type_keyword "void"
  | TSpec_char ->
      pp_colour_type_keyword "char"
  | TSpec_short ->
      pp_colour_type_keyword "short"
  | TSpec_int ->
      pp_colour_type_keyword "int"
  | TSpec_long ->
      pp_colour_type_keyword "long"
  | TSpec_float ->
      pp_colour_type_keyword "float"
  | TSpec_double ->
      pp_colour_type_keyword "double"
  | TSpec_signed ->
      pp_colour_type_keyword "signed"
  | TSpec_unsigned ->
      pp_colour_type_keyword "unsigned"
  | TSpec_Bool ->
      pp_colour_type_keyword "_Bool"
  | TSpec_Complex ->
      pp_colour_type_keyword "_Complex"
  | TSpec_Atomic tyname ->
      pp_colour_keyword "_Atomic" ^^ P.parens (pp_type_name tyname)
  | TSpec_struct (id_opt, s_decls_opt) ->
      pp_colour_keyword "struct" ^^^ P.optional pp_cabs_identifier id_opt ^^^
      P.optional (fun z -> P.braces $ (space_list pp_struct_declaration) z) s_decls_opt
  | TSpec_union (id_opt, s_decls_opt) ->
      pp_colour_keyword "union" ^^^ P.optional pp_cabs_identifier id_opt ^^^
      P.optional (fun z -> P.braces $ (space_list pp_struct_declaration) z) s_decls_opt
  | TSpec_enum (id_opt, enums_opt) ->
      pp_colour_keyword "enum" ^^^ P.optional pp_cabs_identifier id_opt ^^^
      P.optional (fun z -> P.braces $ (space_list pp_enumerator) z) enums_opt
  | TSpec_name id ->
      pp_cabs_identifier id


and pp_struct_declaration = function
  | Struct_declaration (specs, qs, s_decls) ->
      space_list pp_cabs_type_specifier specs ^^^
      space_list pp_cabs_type_qualifier qs    ^^^
      comma_list pp_struct_declarator s_decls ^^ P.semi
  | Struct_assert sa_decl ->
      pp_static_assert_declaration sa_decl

and pp_struct_declarator = function
  | SDecl_simple decltor ->
      pp_declarator decltor
  | SDecl_bitfield (decltor_opt, e) ->
      P.optional pp_declarator decltor_opt ^^ P.colon ^^ pp_cabs_expression None e

and pp_enumerator (id, e_opt) =
  match e_opt with
    | None   -> pp_cabs_identifier id
    | Some e -> pp_cabs_identifier id ^^^ P.equals ^^ pp_cabs_expression None e


and pp_cabs_type_qualifier = function
  | Q_const ->
      pp_colour_keyword "const"
  | Q_restrict ->
      pp_colour_keyword "restrict"
  | Q_volatile ->
      pp_colour_keyword "volatile"
  | Q_Atomic ->
      pp_colour_keyword "_Atomic"


and pp_function_specifier = function
  | FS_inline ->
      pp_colour_keyword "inline"
  | FS_Noreturn ->
      pp_colour_keyword "_Noreturn"


and pp_alignment_specifier = function
  | AS_type tyname ->
      pp_colour_keyword "_Alignas" ^^ P.parens (pp_type_name tyname)
  | AS_expr e ->
      pp_colour_keyword "_Alignas" ^^ P.parens (pp_cabs_expression None e)


and pp_declarator = function
  | Declarator (ptr_decl_opt, ddecl) ->
      P.optional (fun z -> pp_pointer_declarator z ^^ P.space) ptr_decl_opt ^^ pp_direct_declarator ddecl

and pp_direct_declarator = function
  | DDecl_identifier id ->
      pp_cabs_identifier id
  | DDecl_declarator decltor ->
      P.parens (pp_declarator decltor)
  | DDecl_array (ddecltor, abs_decltor) ->
      pp_direct_declarator ddecltor ^^^ pp_array_declarator abs_decltor
  | DDecl_function (ddecltor, param_tys) ->
      pp_direct_declarator ddecltor ^^^ P.parens (pp_parameter_type_list param_tys)
and pp_array_declarator = function
  | ADecl (qs, is_static, a_decltor_size_opt) ->
      P.brackets (
        (if is_static then pp_colour_keyword "static" else P.empty) ^^^
        space_list pp_cabs_type_qualifier qs         ^^^
        P.optional pp_array_declarator_size a_decltor_size_opt
      )
and pp_array_declarator_size = function
  | ADeclSize_expression e ->
      pp_cabs_expression None e
  | ADeclSize_asterisk ->
      !^ "*"

and pp_pointer_declarator = function
  | PDecl (qs, ptr_decltor_opt) ->
      !^ "*" ^^^ space_list pp_cabs_type_qualifier qs ^^
      P.optional (fun z -> P.space ^^ pp_pointer_declarator z) ptr_decltor_opt

and pp_parameter_type_list = function
  | Params (param_decls, false) ->
      comma_list pp_parameter_declaration param_decls
  | Params (param_decls, true) ->
      comma_list pp_parameter_declaration param_decls ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot

and pp_parameter_declaration = function
  | PDeclaration_decl (specifs, decltor) ->
      pp_specifiers specifs ^^ pp_declarator decltor
  | PDeclaration_abs_decl (specifs, abs_decltor_opt) ->
      pp_specifiers specifs ^^ P.optional pp_abstract_declarator abs_decltor_opt


and pp_type_name = function
  | Type_name (specs, qs, a_decltor_opt) ->
      space_list pp_cabs_type_specifier specs ^^^
      space_list pp_cabs_type_qualifier qs    ^^^
      P.optional pp_abstract_declarator a_decltor_opt

and pp_abstract_declarator = function
  | AbsDecl_pointer ptr_decltor ->
      pp_pointer_declarator ptr_decltor
  | AbsDecl_direct (ptr_decltor_opt, dabs_decltor) ->
      P.optional (fun z -> pp_pointer_declarator z ^^ P.space) ptr_decltor_opt ^^
      pp_direct_abstract_declarator dabs_decltor

and pp_direct_abstract_declarator = function
  | DAbs_abs_declarator abs_decltor ->
      P.parens (pp_abstract_declarator abs_decltor)
  | DAbs_array (dabs_decltor_opt, abs_decltor) ->
      P.optional (fun z -> pp_direct_abstract_declarator z ^^ P.space) dabs_decltor_opt ^^ pp_array_declarator abs_decltor
  | DAbs_function (dabs_decltor_opt, param_tys) ->
      P.optional (fun z -> pp_direct_abstract_declarator z ^^ P.space) dabs_decltor_opt ^^ P.parens (pp_parameter_type_list param_tys)

and pp_initializer_ = function
  | Init_expr e ->
      pp_cabs_expression None e
  | Init_list inits ->
      P.braces (pp_initializer_list inits)

and pp_designator = function
  | Desig_array e ->
      P.brackets (pp_cabs_expression None e)
  | Desig_member id ->
      P.dot ^^ pp_cabs_identifier id


and pp_static_assert_declaration = function
 | Static_assert (e, lit) ->
     pp_colour_keyword "_Static_assert" ^^ P.parens (pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_string_literal lit)


and pp_initializer_list inits =
  comma_list (fun (desigs_opt, init) ->
    P.optional (fun z -> space_list pp_designator z ^^^ P.equals ^^ P.space) desigs_opt ^^ pp_initializer_ init
  ) inits


let rec pp_cabs_statement = function
  | CabsSlabel (id, s) ->
      pp_colour_label id ^^ P.colon ^^^ pp_cabs_statement s
  | CabsScase (e, s) ->
      pp_colour_keyword "case" ^^^ pp_cabs_expression None e ^^ P.colon ^^^ pp_cabs_statement s
  | CabsSdefault s ->
      pp_colour_keyword "default" ^^^ pp_cabs_statement s
  | CabsSblock ss ->
      let block = P.separate_map (P.break 1) pp_cabs_statement ss in
      P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
  | CabsSdecl decl ->
      pp_declaration decl
  | CabsSnull ->
      P.semi
  | CabsSexpr e ->
      pp_cabs_expression None e ^^ P.semi
  | CabsSif (e, s1, s2_opt) ->
      pp_colour_keyword "if" ^^^ P.parens (pp_cabs_expression None e) ^^^
      pp_cabs_statement s1 ^^
      P.optional (fun z -> P.space ^^ pp_cabs_statement z) s2_opt
  | CabsSswitch (e, s) ->
      pp_colour_keyword "switch" ^^^ P.parens (pp_cabs_expression None e) ^/^
      pp_cabs_statement s
  | CabsSwhile (e, s) ->
      pp_colour_keyword "while" ^^^ P.parens (pp_cabs_expression None e) ^/^
      pp_cabs_statement s
  | CabsSdo (e, s) ->
      pp_colour_keyword "do" ^/^ pp_cabs_statement s ^/^
      pp_colour_keyword "while" ^^^ P.parens (pp_cabs_expression None e) ^^ P.semi
  | CabsSfor (fc_opt, e1_opt, e2_opt, s) ->
      pp_colour_keyword "for" ^^^ P.parens (
        P.optional pp_for_clause fc_opt ^^ P.semi ^^^
        P.optional (pp_cabs_expression None) e1_opt ^^ P.semi ^^^
        P.optional (pp_cabs_expression None) e2_opt
      ) ^/^
      pp_cabs_statement s
  | CabsSgoto id ->
      pp_colour_keyword "goto" ^^^ pp_colour_label id ^^ P.semi
  | CabsScontinue ->
      pp_colour_keyword "continue" ^^ P.semi
  | CabsSbreak ->
      pp_colour_keyword "break" ^^ P.semi
  | CabsSreturn e_opt ->
      pp_colour_keyword "return" ^^^ P.optional (pp_cabs_expression None) e_opt ^^ P.semi

and pp_for_clause = function
 | FC_expr e ->
     pp_cabs_expression None e
 | FC_decl decl ->
     pp_declaration decl


let pp_function_definition (FunDef (specifs, decltor, stmt)) =
  pp_specifiers specifs ^^ pp_declarator decltor ^^^ pp_cabs_statement stmt

let pp_external_declaration = function
  | EDecl_func fdef -> pp_function_definition fdef
  | EDecl_decl decl -> pp_declaration decl


let pp_translate_unit (TUnit edecls) =
  isatty := Unix.isatty Unix.stdout;
  let pp d def = d ^^ pp_external_declaration def ^^ P.break 1 in
  List.fold_left pp P.empty edecls
*)


(* ================================================================================ *)


let pp_ctor k =
  !^ (if !isatty then ansi_format [Bold; Cyan] k else k)

let pp_option pp = function
  | Some z -> !^ "Some" ^^ P.parens (pp z)
  | None   -> !^ "None"

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
      pp_cabs_integer_constant icst
  | CabsFloating_const str ->
      !^ str
  | CabsEnumeration_const ->
      !^ "WIP[enumeration-constant]"
  | CabsCharacter_const ccst ->
      pp_cabs_character_constant ccst


let pp_cabs_encoding_prefix = function
  | CabsEncPrefix_u8 -> !^ "u8"
  | CabsEncPrefix_u  -> !^ "u"
  | CabsEncPrefix_U  -> !^ "U"
  | CabsEncPrefix_L  -> !^ "L"

let pp_cabs_string_literal (pref_opt, strs) =
  P.optional pp_cabs_encoding_prefix pref_opt ^^ P.dquotes (!^ (String.concat "" strs))


(* DEBUG *)
let pp_comment str = if !isatty then pp_ansi_format [Red] !^ str else !^ str

(*
let pp_loc (start_p, _) =
  pp_comment (
   "/* " ^ Lexing.(
    String.concat ":" [start_p.pos_fname;
                       string_of_int start_p.pos_lnum;
                       string_of_int (start_p.pos_cnum - start_p.pos_bol)
                      ]
  ) ^ " */"
)
*)

let rec pp_cabs_expression p (CabsExpression (loc, expr)) =
  let p' = precedence expr in
  let f = P.group -| pp_cabs_expression p' in
  (if lt_precedence p' p then fun x -> x else P.parens) $
    match expr with
      | CabsEident id ->
          pp_ctor "CabsEident" ^^ P.brackets (pp_cabs_identifier id)
      | CabsEconst cst ->
          pp_ctor "CabsEconst" ^^ P.brackets (pp_cabs_constant cst)
      | CabsEstring str ->
          pp_ctor "CabsEstring" ^^ P.brackets (pp_cabs_string_literal str)
      | CabsEgeneric (e, gs) ->
          pp_ctor "CabsEgeneric" ^^ P.brackets (f e ^^ P.comma ^^^ comma_list pp_cabs_generic_association gs)
      | CabsEsubscript (e1, e2) ->
          pp_ctor "CabsEsubscript" ^^ P.brackets (f e1 ^^ P.comma ^^^ f e2)
      | CabsEcall (e, es) ->
          pp_ctor "CabsEcall" ^^ P.brackets (f e ^^ P.comma ^^^P.brackets (comma_list f es))
      | CabsEassert e ->
          pp_ctor "CabsEassert" ^^ P.brackets (f e)
      | CabsEoffsetof (tyname, ident) ->
          pp_ctor "CabsEoffsetof" ^^ P.brackets (pp_type_name tyname ^^ P.comma ^^^ pp_cabs_identifier ident)
      | CabsEmemberof (e, id) ->
          pp_ctor "CabsEmemberof" ^^ P.brackets (f e ^^ P.comma ^^^ pp_cabs_identifier id)
      | CabsEmemberofptr (e, id) ->
          pp_ctor "CabsEmemberofptr" ^^ P.brackets (f e ^^ P.comma ^^^ pp_cabs_identifier id)
      | CabsEpostincr e ->
          pp_ctor "CabsEpostincr" ^^ P.brackets (f e)
      | CabsEpostdecr e ->
          pp_ctor "CabsEpostdecr" ^^ P.brackets (f e)
      | CabsEcompound (tyname, inits) ->
          pp_ctor "CabsEcompound" ^^ P.brackets (pp_type_name tyname ^^ P.comma ^^^ P.braces (pp_initializer_list inits))
      | CabsEpreincr e ->
          pp_ctor "CabsEpreincr" ^^ P.brackets (f e)
      | CabsEpredecr e ->
          pp_ctor "CabsEpredecr" ^^ P.brackets (f e)
      | CabsEunary (uop, e) ->
          pp_ctor "CabsEunary" ^^ P.brackets (pp_cabs_unary_operator uop ^^ P.comma ^^^ f e)
      | CabsEsizeof_expr e ->
          pp_ctor "CabsEsizeof_expr" ^^ P.brackets (f e)
      | CabsEsizeof_type tyname ->
          pp_ctor "CabsEsizeof_type" ^^ P.brackets (pp_type_name tyname)
      | CabsEalignof tyname ->
          pp_ctor "CabsEalignof" ^^ P.brackets (pp_type_name tyname)
      | CabsEcast (tyname, e) ->
          pp_ctor "CabsEcast" ^^ P.brackets (pp_type_name tyname ^^ P.comma ^^^ f e)
      | CabsEbinary (bop, e1, e2) ->
          pp_ctor "CabsEbinary" ^^ P.brackets (pp_cabs_binary_operator bop ^^ P.comma ^^^ f e1 ^^ P.comma ^^^ f e2)
      | CabsEcond (e1, e2, e3) ->
          pp_ctor "CabsEcond" ^^ P.brackets (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3)
      | CabsEassign (aop, e1, e2) ->
          pp_ctor "CabsEassign" ^^ P.brackets (pp_cabs_assignment_operator aop ^^ P.comma ^^^ f e1 ^^ P.comma ^^^ f e2)
      | CabsEcomma (e1, e2) ->
          pp_ctor "CabsEcomma" ^^ P.brackets (f e1 ^^ P.comma ^^^ f e2)
      | CabsEva_start (e, ident) ->
          pp_ctor "CabsEva_start"  ^^ P.brackets (f e ^^ P.comma ^^^ pp_cabs_identifier ident)
      | CabsEva_arg (e, tyname) ->
          pp_ctor "CabsEva_arg"  ^^ P.brackets (f e ^^ P.comma ^^^ pp_type_name tyname)

and pp_cabs_generic_association = function
  | GA_type (tyname, e) ->
      pp_ctor "GA_type" ^^ P.brackets (pp_type_name tyname ^^ P.comma ^^^ pp_cabs_expression None e)
  | GA_default e ->
      pp_ctor "GA_default" ^^ P.brackets (pp_cabs_expression None e)


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


and pp_declaration = function
  | Declaration_base (specifs, idecls) ->
      pp_ctor "Declaration_base" ^^ P.brackets (pp_specifiers specifs ^^ P.comma ^^^ P.brackets (comma_list pp_init_declarator idecls))
  | Declaration_static_assert sa_decl ->
      pp_ctor "Declaration_static_assert" ^^ P.brackets (pp_static_assert_declaration sa_decl)

(* TODO *)
and pp_specifiers specifs =
  P.braces (
    P.brackets (comma_list pp_storage_class_specifier specifs.storage_classes     ) ^^ P.comma ^^^
    P.brackets (comma_list pp_cabs_type_specifier     specifs.type_specifiers     ) ^^ P.comma ^^^
    P.brackets (comma_list pp_cabs_type_qualifier     specifs.type_qualifiers     ) ^^ P.comma ^^^
    P.brackets (comma_list pp_function_specifier      specifs.function_specifiers ) ^^ P.comma ^^^
    P.brackets (comma_list pp_alignment_specifier     specifs.alignment_specifiers)
  )

(*
  storage_classes:      list storage_class_specifier;
  type_specifiers:      list cabs_type_specifier;
  type_qualifiers:      list cabs_type_qualifier;
  function_specifiers:  list function_specifier;
  alignment_specifiers: list alignment_specifier;
*)


(*
  let zs = List.map pp_storage_class_specifier specifs.storage_classes      @
           List.map pp_cabs_type_specifier     specifs.type_specifiers      @
           List.map pp_cabs_type_qualifier     specifs.type_qualifiers      @
           List.map pp_function_specifier      specifs.function_specifiers  @
           List.map pp_alignment_specifier     specifs.alignment_specifiers in
*)
(*
  space_list pp_storage_class_specifier specifs.storage_classes      ^^ (if specifs.storage_classes      = [] then P.empty else P.space) ^^
  space_list pp_cabs_type_specifier     specifs.type_specifiers      ^^ (if specifs.type_specifiers      = [] then P.empty else P.space) ^^
  space_list pp_cabs_type_qualifier     specifs.type_qualifiers      ^^ (if specifs.type_qualifiers      = [] then P.empty else P.space) ^^
  space_list pp_function_specifier      specifs.function_specifiers  ^^ (if specifs.function_specifiers  = [] then P.empty else P.space) ^^
  space_list pp_alignment_specifier     specifs.alignment_specifiers ^^ (if specifs.alignment_specifiers = [] then P.empty else P.space)
*)

and pp_init_declarator = function
  | InitDecl (_, decltor, None) ->
      pp_ctor "InitDecl" ^^ P.brackets (pp_declarator decltor ^^ P.comma ^^^ !^ "None")
  | InitDecl (_, decltor, Some init) ->
      pp_ctor "InitDecl" ^^ P.brackets (pp_declarator decltor ^^ P.comma ^^^ !^ "Some" ^^^ P.parens (pp_initializer_ init))


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


and pp_cabs_type_specifier = function
  | TSpec_void ->
      pp_ctor "TSpec_void"
  | TSpec_char ->
      pp_ctor "TSpec_char"
  | TSpec_short ->
      pp_ctor "TSpec_short"
  | TSpec_int ->
      pp_ctor "TSpec_int"
  | TSpec_long ->
      pp_ctor "TSpec_long"
  | TSpec_float ->
      pp_ctor "TSpec_float"
  | TSpec_double ->
      pp_ctor "TSpec_double"
  | TSpec_signed ->
      pp_ctor "TSpec_signed"
  | TSpec_unsigned ->
      pp_ctor "TSpec_unsigned"
  | TSpec_Bool ->
      pp_ctor "TSpec__Bool"
  | TSpec_Complex ->
      pp_ctor "TSpec__Complex"
  | TSpec_Atomic tyname ->
      pp_ctor "TSpec_Atomic" ^^ P.brackets (pp_type_name tyname)
  | TSpec_struct (id_opt, s_decls_opt) ->
      pp_ctor "TSpec_struct" ^^ P.brackets (
        pp_option pp_cabs_identifier id_opt ^^ P.comma ^^^
        pp_option (fun z -> P.brackets $ (comma_list pp_struct_declaration) z) s_decls_opt
      )
  | TSpec_union (id_opt, s_decls_opt) ->
      pp_ctor "TSpec_union" ^^ P.brackets (
        pp_option pp_cabs_identifier id_opt ^^ P.comma ^^^
        pp_option (fun z -> P.brackets $ (comma_list pp_struct_declaration) z) s_decls_opt
      )
  | TSpec_enum (id_opt, enums_opt) ->
      pp_ctor "TSpec_enum" ^^ P.brackets (
        pp_option pp_cabs_identifier id_opt ^^ P.comma ^^^
        pp_option (fun z -> P.brackets $ (comma_list pp_enumerator) z) enums_opt
      )
  | TSpec_name id ->
      pp_ctor "TSpec_name" ^^ P.brackets (pp_cabs_identifier id)


and pp_struct_declaration = function
  | Struct_declaration (specs, qs, s_decls) ->
      pp_ctor "Struct_declaration" ^^ P.brackets (
        P.brackets (comma_list pp_cabs_type_specifier specs) ^^ P.comma ^^^
        P.brackets (comma_list pp_cabs_type_qualifier qs) ^^ P.comma ^^^
        P.brackets (comma_list pp_struct_declarator s_decls)
      )
  | Struct_assert sa_decl ->
      pp_ctor "Struct_assert" ^^ P.brackets (pp_static_assert_declaration sa_decl)

and pp_struct_declarator = function
  | SDecl_simple decltor ->
      pp_ctor "SDecl_simple" ^^ P.brackets (pp_declarator decltor)
  | SDecl_bitfield (decltor_opt, e) ->
      pp_ctor "SDecl_bitfield" ^^ P.brackets (pp_option pp_declarator decltor_opt ^^ P.comma ^^^ pp_cabs_expression None e)

and pp_enumerator (id, e_opt) =
  P.parens (pp_cabs_identifier id ^^^ P.comma ^^^ pp_option (pp_cabs_expression None) e_opt)


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


and pp_alignment_specifier = function
  | AS_type tyname ->
      pp_ctor "AS_type" ^^ P.brackets (pp_type_name tyname)
  | AS_expr e ->
      pp_ctor "AS_expr" ^^ P.brackets (pp_cabs_expression None e)


and pp_declarator = function
  | Declarator (ptr_decl_opt, ddecl) ->
      pp_ctor "Declarator" ^^ P.brackets (
        pp_option pp_pointer_declarator ptr_decl_opt ^^ P.comma ^^^
        pp_direct_declarator ddecl
      )

and pp_direct_declarator = function
  | DDecl_identifier id ->
      pp_ctor "DDecl_identifier" ^^ P.brackets (pp_cabs_identifier id)
  | DDecl_declarator decltor ->
      pp_ctor "DDecl_declarator" ^^ P.brackets (pp_declarator decltor)
  | DDecl_array (ddecltor, abs_decltor) ->
      pp_ctor "DDecl_array" ^^ P.brackets (
        pp_direct_declarator ddecltor ^^ P.comma ^^^
        pp_array_declarator abs_decltor
      )
  | DDecl_function (ddecltor, param_tys) ->
      pp_ctor "DDecl_function" ^^ P.brackets (
        pp_direct_declarator ddecltor ^^ P.comma ^^^
        P.brackets (pp_parameter_type_list param_tys)
      )
and pp_array_declarator = function
  | ADecl (_, qs, is_static, a_decltor_size_opt) ->
      pp_ctor "ADecl" ^^ P.brackets (
        P.brackets (comma_list pp_cabs_type_qualifier qs) ^^ P.comma ^^^
        pp_bool is_static ^^ P.comma ^^
        pp_option pp_array_declarator_size a_decltor_size_opt
      )
and pp_array_declarator_size = function
  | ADeclSize_expression e ->
      pp_ctor "ADEclSize_expression" ^^ P.brackets (pp_cabs_expression None e)
  | ADeclSize_asterisk ->
      pp_ctor "ADeclSize_asterisk"

and pp_pointer_declarator = function
  | PDecl (qs, ptr_decltor_opt) ->
      pp_ctor "PDecl" ^^ P.brackets (
        P.brackets (comma_list pp_cabs_type_qualifier qs) ^^ P.comma ^^^
        pp_option pp_pointer_declarator ptr_decltor_opt
      )

and pp_parameter_type_list = function
  | Params (param_decls, false) ->
      pp_ctor "Params" ^^ P.brackets (comma_list pp_parameter_declaration param_decls ^^ P.comma ^^^ !^ "false")
  | Params (param_decls, true) ->
      pp_ctor "Params" ^^ P.brackets (comma_list pp_parameter_declaration param_decls ^^ P.comma ^^^ !^ "true")

and pp_parameter_declaration = function
  | PDeclaration_decl (specifs, decltor) ->
      pp_ctor "PDeclaration_decl" ^^ P.brackets (pp_specifiers specifs ^^ P.comma ^^^ pp_declarator decltor)
  | PDeclaration_abs_decl (specifs, abs_decltor_opt) ->
      pp_ctor "PDeclaration_abs_decl" ^^ P.brackets (
        pp_specifiers specifs ^^ P.comma ^^^
        pp_option pp_abstract_declarator abs_decltor_opt
      )


and pp_type_name = function
  | Type_name (specs, qs, a_decltor_opt) ->
      pp_ctor "Type_name" ^^ P.brackets (
        P.brackets (comma_list pp_cabs_type_specifier specs) ^^ P.comma ^^^
        P.brackets (comma_list pp_cabs_type_qualifier qs) ^^ P.comma ^^^
        pp_option pp_abstract_declarator a_decltor_opt
      )

and pp_abstract_declarator = function
  | AbsDecl_pointer ptr_decltor ->
      pp_ctor "AbsDecl_pointer" ^^ P.brackets (pp_pointer_declarator ptr_decltor)
  | AbsDecl_direct (ptr_decltor_opt, dabs_decltor) ->
      pp_ctor "AbsDecl_direct" ^^ P.brackets (
        pp_option pp_pointer_declarator ptr_decltor_opt ^^ P.comma ^^^
        pp_direct_abstract_declarator dabs_decltor
      )

and pp_direct_abstract_declarator = function
  | DAbs_abs_declarator abs_decltor ->
      pp_ctor "DAbs_abs_declarator" ^^ P.brackets (pp_abstract_declarator abs_decltor)
  | DAbs_array (dabs_decltor_opt, abs_decltor) ->
      pp_ctor "DAbs_array" ^^ P.brackets (
        pp_option pp_direct_abstract_declarator dabs_decltor_opt ^^ P.comma ^^^
        pp_array_declarator abs_decltor
      )
  | DAbs_function (dabs_decltor_opt, param_tys) ->
      pp_ctor "DAbs_function" ^^ P.brackets (
        pp_option pp_direct_abstract_declarator dabs_decltor_opt ^^ P.comma ^^^
        P.parens (pp_parameter_type_list param_tys)
      )

and pp_initializer_ = function
  | Init_expr e ->
      pp_ctor "Init_expr" ^^ P.brackets (pp_cabs_expression None e)
  | Init_list inits ->
      pp_ctor "Init_list" ^^ P.brackets (pp_initializer_list inits)

and pp_designator = function
  | Desig_array e ->
      pp_ctor "Desig_array" ^^ P.brackets (pp_cabs_expression None e)
  | Desig_member id ->
      pp_ctor "Desig_member" ^^ P.brackets (pp_cabs_identifier id)


and pp_static_assert_declaration = function
 | Static_assert (e, lit) ->
     pp_ctor "Static_assert" ^^ P.brackets (
       pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_string_literal lit
     )


(* TODO *)
and pp_initializer_list inits =
  comma_list (fun (desigs_opt, init) ->
    P.optional (fun z -> space_list pp_designator z ^^^ P.equals ^^ P.space) desigs_opt ^^ pp_initializer_ init
  ) inits


let rec pp_cabs_statement (CabsStatement (loc, stmt_)) =
  match stmt_ with
  | CabsSlabel (id, s) ->
      pp_ctor "CabsSlabel" ^^ P.brackets (pp_colour_label id ^^ P.comma ^^^ pp_cabs_statement s)
  | CabsScase (e, s) ->
      pp_ctor "CabsScase" ^^ P.brackets (pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_statement s)
  | CabsSdefault s ->
      pp_ctor "CabsSdefault" ^^ P.brackets (pp_cabs_statement s)
  | CabsSblock ss ->
      pp_ctor "CabsSblock" ^^ P.brackets (P.brackets (comma_list pp_cabs_statement ss))
  | CabsSdecl decl ->
      pp_ctor "CabsSdecl" ^^ P.brackets (pp_declaration decl)
  | CabsSnull ->
      pp_ctor "CabsSnull"
  | CabsSexpr e ->
      pp_ctor "CabsSexpr" ^^ P.brackets (pp_cabs_expression None e)
  | CabsSif (e, s1, s2_opt) ->
      pp_ctor "CabsSif" ^^ P.brackets (
        pp_cabs_expression None e ^^ P.comma ^^^
        pp_cabs_statement s1 ^^
        pp_option pp_cabs_statement s2_opt
      )
  | CabsSswitch (e, s) ->
      pp_ctor "CabsSswitch" ^^ P.brackets (pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_statement s)
  | CabsSwhile (e, s) ->
      pp_ctor "CabsSwhile" ^^ P.brackets (pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_statement s)
  | CabsSdo (e, s) ->
      pp_ctor "CabsSdo" ^^ P.brackets (pp_cabs_expression None e ^^ P.comma ^^^ pp_cabs_statement s)
  | CabsSfor (fc_opt, e1_opt, e2_opt, s) ->
      pp_ctor "CabsSfor" ^^ P.brackets (
        pp_option pp_for_clause fc_opt ^^ P.comma ^^^
        pp_option (pp_cabs_expression None) e1_opt ^^ P.comma ^^^
        pp_option (pp_cabs_expression None) e2_opt ^^ P.comma ^^^
        pp_cabs_statement s
      )
  | CabsSgoto id ->
      pp_ctor "CabsSgoto" ^^ P.brackets (pp_colour_label id)
  | CabsScontinue ->
      pp_ctor "CabsScontinue"
  | CabsSbreak ->
      pp_ctor "CabsSbreak"
  | CabsSreturn e_opt ->
      pp_ctor "CabsSreturn" ^^ P.brackets (pp_option (pp_cabs_expression None) e_opt)
  | CabsSpar ss ->
      pp_ctor "CabsSpar" ^^ P.brackets (P.brackets (comma_list pp_cabs_statement ss))


and pp_for_clause = function
 | FC_expr e ->
     pp_ctor "FC_expr" ^^ P.brackets (pp_cabs_expression None e)
 | FC_decl decl ->
     pp_ctor "FC_decl" ^^ P.brackets (pp_declaration decl)


let pp_function_definition (FunDef (specifs, decltor, stmt)) =
  pp_ctor "Fundef" ^^ P.brackets (pp_specifiers specifs ^^ P.comma ^^^ pp_declarator decltor ^^ P.comma ^^^ pp_cabs_statement stmt)

let pp_external_declaration = function
  | EDecl_func fdef -> pp_ctor "EDecl_func" ^^ P.brackets (pp_function_definition fdef)
  | EDecl_decl decl -> pp_ctor "EDecl_decl" ^^ P.brackets (pp_declaration decl)


let pp_translate_unit (TUnit edecls) =
  isatty := Unix.isatty Unix.stdout;
  let pp d def = d ^^ pp_external_declaration def ^^ P.break 1 in
  List.fold_left pp P.empty edecls
