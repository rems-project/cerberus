open Global
open Cabs0

open Colour

let ($) f x = f x
let (-|) f g x = f (g x)

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | Evariable _
  | Econstant _
  | Eoffsetof _ -> Some 0
  
  | Esubscript _
  
(*
  | C11_ATOMIC_INIT _
  | C11_ATOMIC_STORE _
  | C11_ATOMIC_LOAD _
  | C11_ATOMIC_EXCHANGE _
  | C11_ATOMIC_COMPARE_EXCHANGE_STRONG _
  | C11_ATOMIC_COMPARE_EXCHANGE_WEAK _
  | C11_ATOMIC_FETCH_KEY _
*)
  
  | Ecall0 _
  | Ememberof _
  | Ememberofptr _
  | Eunary (PostfixIncr0, _)
  | Eunary (PostfixDecr0, _) -> Some 1
  
  | Eunary _
  | Ecast _
  | Eexpr_sizeof _
  | Etype_sizeof _
  | Ealignof _ -> Some 2
  
  | Ebinary (Mul0, _, _)
  | Ebinary (Div0, _, _)
  | Ebinary (Mod0, _, _) -> Some 3
  
  | Ebinary (Add0, _, _)
  | Ebinary (Sub0, _, _) -> Some 4
  
  | Ebinary (Shl0, _, _)
  | Ebinary (Shr0, _, _) -> Some 5
  
  | Ebinary (Lt0, _, _)
  | Ebinary (Gt0, _, _)
  | Ebinary (Le0, _, _)
  | Ebinary (Ge0, _, _) -> Some 6
  
  | Ebinary (Eq0, _, _)
  | Ebinary (Ne0, _, _) -> Some 7
  
  | Ebinary (Band0, _, _) -> Some 8
  
  | Ebinary (Xor0, _, _) -> Some 9
  
  | Ebinary (Bor0, _, _) -> Some 10
  
  | Ebinary (And0, _, _) -> Some 11
  
  | Ebinary (Or0, _, _) -> Some 12
  
  | Econditional _ -> Some 13
  
  | Ebinary (Assign0, _, _)
  | Ebinary (Add_assign, _, _)
  | Ebinary (Sub_assign, _, _)
  | Ebinary (Mul_assign, _, _)
  | Ebinary (Div_assign, _, _)
  | Ebinary (Mod_assign, _, _)
  | Ebinary (Band_assign, _, _)
  | Ebinary (Bor_assign, _, _)
  | Ebinary (Xor_assign, _, _)
  | Ebinary (Shl_assign, _, _)
  | Ebinary (Shr_assign, _, _) -> Some 14
  
  | Ebinary (Comma0, _, _) -> Some 15
  
  (* | BUILTIN_VA_ARG _ *)


let lt_precedence p1 p2 =
  match p1, p2 with
    | Some n1, Some n2 -> n1 < n2
    | Some _ , None    -> true
    | None   , _       -> false


let pp_keyword  w = !^ (ansi_format [Bold; Cyan] w)
let pp_type     t = !^ (ansi_format [Green] t)
let pp_constant c = !^ (ansi_format [Magenta] c)
let pp_number   n = !^ (ansi_format [Yellow] n)









let pp_list pp zs =
  let rec f = function
    | []    -> P.empty
    | [z]   -> pp z
    | z::zs -> pp z ^^ P.semi ^^^ f zs in
  P.brackets (f zs)

let pp_option pp = function
  | Some z -> !^ "Some" ^^^ pp z
  | None   -> !^ "None"

let pp_bool = function
  | true  -> !^ "true"
  | false -> !^ "false"

let pp_atom str =
  P.dquotes $ P.string str

let pp_highlight z =
  P.parens (!^ "\x1b[31m" ^^ z ^^ !^ "\x1b[0m")


let rec pp_typeSpecifier = function
  | T_void ->
      !^ "Tvoid"
  | T_char ->
      !^ "Tchar"
  | T_short ->
      !^ "Tshort"
  | T_int ->
      !^ "Tint"
  | T_long ->
      !^ "Tlong"
  | T_float ->
      !^ "Tfloat"
  | T_double ->
      !^ "Tdouble"
  | T_signed ->
      !^ "Tsigned"
  | T_unsigned ->
      !^ "Tunsigned"
  | T_Bool ->
      !^ "T_Bool"
  | T_named str ->
      !^ "Tnamed" ^^^ pp_atom str

  | T_atomic (spec_elems, decl_t) ->
    !^ "Tatomic" ^^^ P.parens (
      pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
      pp_decl_type decl_t
    )
  
  | T_struct (str_opt, fg_opt, []) -> 
      !^ "Tstruct" ^^^ P.parens (
        pp_option pp_atom str_opt ^^ P.comma ^^^
        pp_option (pp_list pp_field_group) fg_opt ^^ P.comma ^^^
        (* TODO *)
        !^ "[]"
      )
  | T_union (str_opt, fg_opt, []) ->
      !^ "Tunion" ^^^ P.parens (
        pp_option pp_atom str_opt ^^ P.comma ^^^
        pp_option (pp_list pp_field_group) fg_opt ^^ P.comma ^^^
        (* TODO *)
        !^ "[]"
      )
  | T_enum (str_opt, xs_opt, []) ->
      (* TODO *)
      !^ "Tenum[TODO]"


and pp_storage = function
  | SC_auto ->
      !^ "AUTO"
  | SC_static ->
      !^ "STATIC"
  | SC_extern ->
      !^ "EXTERN"
  | SC_register ->
      !^ "REGISTER"
  | SC_Thread_local ->
      !^ "THREAD_LOCAL"
  | SC_typedef ->
      !^ "TYPEDEF"


and pp_type_qualifier = function
  | Q_const ->
      !^ "CV_CONST"
  | Q_volatile ->
      !^ "CV_VOLATILE"
  | Q_restrict ->
      !^ "CV_RESTRICT"
  | Q_Atomic ->
      !^ "CV_ATOMIC"

and pp_spec_elem = function
  | SpecQualifier qual ->
      !^ "SpecCV" ^^^ pp_type_qualifier qual
  | SpecAttr attr ->
      !^ "SpecAttr" ^^^ pp_attribute attr
  | SpecStorage st ->
      !^ "SpecStorage" ^^^ pp_storage st
  | SpecInline ->
      !^ "SpecInline"
  | SpecType tSpec ->
      !^ "SpecType" ^^^ P.parens (pp_typeSpecifier tSpec)


and pp_decl_type = function
 | JUSTBASE ->
     !^ "JUSTBASE"
 | ARRAY (decl_t, quals, attrs, e_opt) ->
     !^ "ARRAY" ^^^ P.parens (
       pp_decl_type decl_t ^^ P.comma ^^^
       pp_list pp_type_qualifier quals ^^ P.comma ^^^
       pp_list pp_attribute attrs ^^ P.comma ^^^
       pp_option (pp_expression None) e_opt
      )
 | PTR (quals, attrs, decl_t) ->
     !^ "PTR" ^^^ P.parens (
       pp_list pp_type_qualifier quals ^^ P.comma ^^^
       pp_list pp_attribute attrs ^^ P.comma ^^^
       pp_decl_type decl_t
     )
 | PROTO (decl_t, (params, is_va)) ->
     !^ "PROTO" ^^^ P.parens (
       pp_decl_type decl_t ^^ P.comma ^^^
       P.parens (pp_list pp_parameter params ^^ P.comma ^^^ pp_bool is_va)
     )


and pp_parameter (PARAM (spec_elems, str_opt, decl_t, attrs, _)) =
  !^ "PARAM" ^^^ P.parens (
    pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
    pp_option pp_atom str_opt ^^ P.comma ^^^
    pp_decl_type decl_t  ^^ P.comma ^^^
    pp_list pp_attribute attrs
  )


and pp_field_group (Field_group (spec_elems, xs, _)) =
  !^ "Field_group" ^^^ P.parens (
    pp_list pp_spec_elem spec_elems ^^ P.comma ^^^ 
    pp_list (fun (x,y) -> P.parens (pp_option pp_name x ^^ P.comma ^^^
                                    pp_option (pp_expression None) y)) xs
  )


and pp_name (Name (str, decl_t, attrs, _)) =
  !^ "Name" ^^^ P.parens (
    pp_atom str ^^ P.comma ^^^
    pp_decl_type decl_t  ^^ P.comma ^^^
    pp_list pp_attribute attrs
  )


and pp_init_name (Init_name (n, ie)) =
  !^ "Init_name" ^^^ P.parens (
    pp_name n ^^ P.comma ^^^
    pp_init_expression ie
  )

and pp_binary_operator = function
  | Add0         -> P.plus
  | Sub0         -> P.minus
  | Mul0         -> P.star
  | Div0         -> P.slash
  | Mod0         -> P.percent
  | And0         -> P.ampersand ^^ P.ampersand
  | Or0          -> P.bar ^^ P.bar
  | Band0        -> P.ampersand
  | Bor0         -> P.bar
  | Xor0         -> P.caret
  | Shl0         -> P.langle ^^ P.langle
  | Shr0         -> P.rangle ^^ P.rangle
  | Eq0          -> P.equals ^^ P.equals
  | Ne0          -> P.bang   ^^ P.equals
  | Lt0          -> P.langle
  | Gt0          -> P.rangle
  | Le0          -> P.langle ^^ P.equals
  | Ge0          -> P.rangle ^^ P.equals
  | Assign0      -> P.equals
  | Add_assign  -> P.equals ^^ P.plus
  | Sub_assign  -> P.equals ^^ P.minus
  | Mul_assign  -> P.equals ^^ P.star
  | Div_assign  -> P.equals ^^ P.slash
  | Mod_assign  -> P.equals ^^ P.percent
  | Band_assign -> P.equals ^^ P.ampersand
  | Bor_assign  -> P.equals ^^ P.bar
  | Xor_assign  -> P.equals ^^ P.caret
  | Shl_assign  -> P.equals ^^ P.langle ^^ P.langle
  | Shr_assign  -> P.equals ^^ P.rangle ^^ P.rangle
  | Comma0       -> P.comma


and pp_unary_operator = function
  | Minus0   -> P.minus
  | Plus0    -> P.plus
  | Not     -> P.bang
  | Bnot0    -> P.tilde
  | Indirection0   -> P.star
  | Address1  -> P.ampersand
  | PrefixIncr -> P.plus ^^ P.plus
  | PrefixDecr -> P.minus ^^ P.minus
  | PostfixIncr0 -> P.plus ^^ P.plus
  | PostfixDecr0 -> P.minus ^^ P.minus


and pp_expression p expr =
  let p' = precedence expr in
  let f = P.group -| pp_expression p' in
  (if lt_precedence p' p then fun x -> x else P.parens) $
    match expr with
      | Eunary (PostfixIncr0 as uop, e)
      | Eunary (PostfixDecr0 as uop, e) ->
          f e ^^ pp_unary_operator uop
      | Eunary (uop, e) ->
          pp_unary_operator uop ^^ f e
      | Ebinary (bop, e1, e2) ->
          f e1 ^^^ pp_binary_operator bop ^^^ f e2
      | Econditional (e1, e2, e3) ->
          P.group (f e1 ^^^ P.qmark ^/^ f e2 ^^^ P.colon ^/^ f e3)
      | Ecast ((spec_elems, decl_t), ie) ->
          pp_highlight $
            !^ "CAST" ^^^ P.parens (
              P.parens (
                pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
                pp_decl_type decl_t
              ) ^^ P.comma ^^^ pp_init_expression ie
            )
(*
      | C11_ATOMIC_INIT (e1, e2) ->
          !^ "__c11_atomic_init" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2)
      | C11_ATOMIC_STORE (e1, e2, e3) ->
          !^ "__c11_atomic_store" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3)
      | C11_ATOMIC_LOAD (e1, e2) ->
          !^ "__c11_atomic_load" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2)
      | C11_ATOMIC_EXCHANGE (e1, e2, e3) ->
          !^ "__c11_atomic_exchange" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3)
      | C11_ATOMIC_COMPARE_EXCHANGE_STRONG (e1, e2, e3, e4, e5) ->
          !^ "__c11_atomic_compare_exchange_strong" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3 ^^ P.comma ^^^ f e3 ^^ P.comma ^^^ f e5)
      | C11_ATOMIC_COMPARE_EXCHANGE_WEAK (e1, e2, e3, e4, e5) ->
          !^ "__c11_atomic_compare_exchange_weak" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3 ^^ P.comma ^^^ f e3 ^^ P.comma ^^^ f e5)
      | C11_ATOMIC_FETCH_KEY (e1, e2, e3) ->
          !^ "__c11_atomic_fetch_key" ^^
          P.parens (f e1 ^^ P.comma ^^^ f e2 ^^ P.comma ^^^ f e3)
*)
      
      | Ecall0 (e, es) ->
          f e ^^ P.parens (comma_list f es)
(*  | BUILTIN_VA_ARG of expression * (list spec_elem * decl_type) *)
      | Econstant c ->
          pp_constant c
      | Evariable str ->
          !^ str
      | Eexpr_sizeof e ->
          pp_keyword "sizeof" ^^^ f e
      | Etype_sizeof (spec_elems, decl_t) ->
          pp_highlight $
            !^ "TYPE_SIZEOF" ^^^ P.parens (
              pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
              pp_decl_type decl_t
            )
      | Ealignof (spec_elems, decl_t) ->
          pp_highlight $
            !^ "ALIGNOF" ^^^ P.parens (
              pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
              pp_decl_type decl_t
            )
      | Esubscript (e1 ,e2) ->
          f e1 ^^ P.brackets (f e2)
      | Ememberof (e, str) ->
          f e ^^ P.dot ^^ (!^ str)
      | Ememberofptr (e, str) ->
          f e ^^ (!^ "->") ^^ (!^ str)
      | Eoffsetof ((spec_elems, decl_t), str) ->
          !^ "OFFSEOF[TODO]"


and pp_integer_suffix = function
  | SUFFIX_UNSIGNED           -> !^ "u"
  | SUFFIX_UNSIGNED_LONG      -> !^ "ul"
  | SUFFIX_UNSIGNED_LONG_LONG -> !^ "ull"
  | SUFFIX_LONG               -> !^ "l"
  | SUFFIX_LONG_LONG          -> !^ "ll"


and pp_character_prefix = function
  | PREFIX_L -> !^ "L"
  | PREFIX_u -> !^ "u"
  | PREFIX_U -> !^ "U"


and pp_encoding_prefix = function
  | ENCODING_u8 -> !^ "u8"
  | ENCODING_u  -> !^ "u"
  | ENCODING_U  -> !^ "U"
  | ENCODING_L  -> !^ "L"


and pp_constant = function
  | CONST_INT (str, suff_opt) ->
      pp_number str ^^ P.optional pp_integer_suffix suff_opt
  | CONST_FLOAT str ->
      pp_number str
  | CONST_CHAR (pref_opt, str) ->
      P.optional pp_character_prefix pref_opt ^^ P.squotes (!^ str)
  | CONST_STRING str ->
      P.dquotes (!^ str)


and pp_init_expression = function
  | NO_INIT ->
      P.empty
  | SINGLE_INIT e ->
      pp_expression None e
  | COMPOUND_INIT xs ->
      P.braces $
        comma_list (fun (iws, ie) ->
          P.separate_map P.space pp_initwhat iws ^^^ P.equals ^^^ pp_init_expression ie
        ) xs


and pp_initwhat = function
  | INFIELD_INIT str ->
      P.dot ^^ !^ str
  | ATINDEX_INIT e ->
      P.brackets (pp_expression None e)


and pp_attribute (ATTR (str, es)) =
  !^ "ATTR" ^^^ P.parens (
    pp_atom str ^^ P.comma ^^^
    pp_list (pp_expression None) es
  )


let pp_init_name_group (spec_elems, ins) =
  P.parens (
    pp_list pp_spec_elem spec_elems ^^ P.comma ^^^
    pp_list pp_init_name ins
  )




let pp_name_group (spec_elems, ns) =
  P.separate_map P.space pp_spec_elem spec_elems ^^^
  P.separate_map P.space pp_name ns


let rec pp_definition = function
 | FUNDEF (spec_elems, n, s, _) ->
     !^ (ansi_format [Bold; Red] "FUNDEF:") ^^^ P.separate_map P.space pp_spec_elem spec_elems ^^^
     pp_name n ^^^ pp_statement s
 | DECDEF (ing, _) ->
     !^ "DECDEF" ^^^ pp_init_name_group ing
(* | PRAGMA (str, _) -> assert false *)


and pp_statement = function
 | Sskip _ ->
     P.semi
 | Sexpression (e, _) ->
     pp_expression None e ^^ P.semi
 | Sblock (ss, _) ->
     let block = P.separate_map (P.break 1) pp_statement ss in
     P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
 | Sif (e, s1, s2_opt, _) ->
     pp_keyword "if" ^^^ P.parens (pp_expression None e) ^^^ pp_statement s1 ^^
     P.optional (fun z -> P.space ^^ pp_keyword "else" ^^^ pp_statement z) s2_opt
 | Swhile (e, s, _) ->
     pp_keyword "while" ^^^ P.parens (pp_expression None e) ^/^ pp_statement s
 | Sdo (e, s, _) ->
     pp_keyword "do" ^/^ pp_statement s ^/^
       pp_keyword "while" ^^^ P.parens (pp_expression None e)
 | Sfor (fc_opt, e2_opt, e3_opt, s, _) ->
     pp_keyword "for" ^^^
     P.parens (P.optional pp_for_clause fc_opt ^^ P.semi ^^^
               P.optional (pp_expression None) e2_opt ^^ P.semi ^^^
               P.optional (pp_expression None) e3_opt) ^/^ pp_statement s
 | Sbreak _ ->
     pp_keyword "break" ^^ P.semi
 | Scontinue _ ->
     pp_keyword "continue" ^^ P.semi
 | Sreturn (e_opt, _) ->
     pp_keyword "return" ^^
     P.optional (fun z -> P.space ^^ pp_expression None z) e_opt ^^ P.semi
 | Sswitch (e, s, _) ->
     pp_keyword "switch" ^^^ P.parens (pp_expression None e) ^/^ pp_statement s
 | Scase (e, s, _) ->
     pp_expression None e ^^ P.colon ^^^ pp_statement s
 | Sdefault (s, _) ->
     pp_keyword "default" ^^ P.colon ^^^ pp_statement s
 | Slabel (str, s, _) ->
     !^ str ^^ P.colon ^^^ pp_statement s
 | Sgoto (str, _) ->
     pp_keyword "goto" ^^^ !^ str ^^ P.semi
 | Sdefinition def ->
     pp_definition def
 | Spar (ss, _) ->
     let threads = P.separate_map (P.space ^^ P.bar ^^ P.bar ^^ P.bar ^^ P.space)
                                  (fun s -> P.nest 2 (pp_statement s)) ss in
     P.lbrace ^^ P.lbrace ^^ P.lbrace ^^^
     threads ^^^
     P.rbrace ^^ P.rbrace ^^ P.rbrace


and pp_for_clause = function
 | FC_EXP e ->
     pp_expression None e
 | FC_DECL (DECDEF (ing, _)) ->
     pp_init_name_group ing



let pp_file defs =
  let pp d def = d ^^ pp_definition def ^^ P.break 1 in
  List.fold_left pp P.empty defs
