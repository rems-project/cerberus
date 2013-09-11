open Global
open Cparser.Cabs0

open Colour

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | VARIABLE _
  | CONSTANT _
  | OFFSETOF _ -> Some 0
  
  | INDEX _
  
  | C11_ATOMIC_INIT _
  | C11_ATOMIC_STORE _
  | C11_ATOMIC_LOAD _
  | C11_ATOMIC_EXCHANGE _
  | C11_ATOMIC_COMPARE_EXCHANGE_STRONG _
  | C11_ATOMIC_COMPARE_EXCHANGE_WEAK _
  | C11_ATOMIC_FETCH_KEY _
  
  | CALL _
  | MEMBEROF _
  | MEMBEROFPTR _
  | UNARY (POSINCR, _)
  | UNARY (POSDECR, _) -> Some 1
  
  | UNARY _
  | CAST _
  | EXPR_SIZEOF _
  | TYPE_SIZEOF _
  | ALIGNOF _ -> Some 2
  
  | BINARY (MUL, _, _)
  | BINARY (DIV, _, _)
  | BINARY (MOD, _, _) -> Some 3
  
  | BINARY (ADD, _, _)
  | BINARY (SUB, _, _) -> Some 4
  
  | BINARY (SHL, _, _)
  | BINARY (SHR, _, _) -> Some 5
  
  | BINARY (LT, _, _)
  | BINARY (GT, _, _)
  | BINARY (LE, _, _)
  | BINARY (GE, _, _) -> Some 6
  
  | BINARY (EQ, _, _)
  | BINARY (NE, _, _) -> Some 7
  
  | BINARY (BAND, _, _) -> Some 8
  
  | BINARY (XOR, _, _) -> Some 9
  
  | BINARY (BOR, _, _) -> Some 10
  
  | BINARY (AND, _, _) -> Some 11
  
  | BINARY (OR, _, _) -> Some 12
  
  | QUESTION _ -> Some 13
  
  | BINARY (ASSIGN, _, _)
  | BINARY (ADD_ASSIGN, _, _)
  | BINARY (SUB_ASSIGN, _, _)
  | BINARY (MUL_ASSIGN, _, _)
  | BINARY (DIV_ASSIGN, _, _)
  | BINARY (MOD_ASSIGN, _, _)
  | BINARY (BAND_ASSIGN, _, _)
  | BINARY (BOR_ASSIGN, _, _)
  | BINARY (XOR_ASSIGN, _, _)
  | BINARY (SHL_ASSIGN, _, _)
  | BINARY (SHR_ASSIGN, _, _) -> Some 14
  
  | BINARY (COMMA, _, _) -> Some 15
  
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



let rec pp_typeSpecifier = function
  | Tvoid      -> pp_type "void"
  | Tchar      -> pp_type "char"
  | Tshort     -> pp_type "short"
  | Tint       -> pp_type "int"
  | Tlong      -> pp_type "long"
  | Tfloat     -> pp_type "float"
  | Tdouble    -> pp_type "double"
  | Tsigned    -> pp_type "signed"
  | Tunsigned  -> pp_type "unsigned"
  | T_Bool     -> pp_type "_Bool"
  | Tnamed str -> pp_type str
  | Tatomic (spec_elems, decl_t) ->
    pp_type "_Atomic" ^^
    P.parens (pp_decl_type decl_t $ P.separate_map P.space pp_spec_elem spec_elems)
  
  | Tstruct (str_opt, fg_opt, []) -> 
      pp_keyword "struct" ^^
      (P.optional (fun z -> P.space ^^ pp_type z) str_opt) ^^
      P.optional (fun z ->
        let block = P.separate_map (P.semi ^^ P.break 1) pp_field_group z in
        P.space ^^ P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
      ) fg_opt
  | Tunion (str_opt, fg_opt, []) ->
      pp_keyword "union" ^^
      (P.optional (fun z -> P.space ^^ pp_type z) str_opt) ^^
      P.optional (fun z ->
        let block = P.separate_map (P.semi ^^ P.break 1) pp_field_group z in
        P.space ^^ P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
      ) fg_opt
  | Tenum (str_opt, xs_opt, []) ->
      pp_keyword "enum" ^^
      (P.optional (fun z -> P.space ^^ pp_type z) str_opt) ^^
      P.optional (fun z ->
        let block = P.separate_map (P.comma ^^ P.break 1) (fun ((str, e_opt), _) ->
          P.space ^^ !^ str ^^
          P.optional (fun z -> P.space ^^ P.equals ^^^ pp_expression None z) e_opt) z in
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
      ) xs_opt


and pp_storage = function
  | AUTO         -> pp_keyword "auto"
  | STATIC       -> pp_keyword "static"
  | EXTERN       -> pp_keyword "extern"
  | REGISTER     -> pp_keyword "register"
  | THREAD_LOCAL -> pp_keyword "_Thread_local"
  | TYPEDEF      -> pp_keyword "typedef"


and pp_cvspec = function
  | CV_CONST    -> pp_keyword "const"
  | CV_VOLATILE -> pp_keyword "volatile"
  | CV_RESTRICT -> pp_keyword "restrict"
  | CV_ATOMIC   -> pp_keyword "_Atomic"


and pp_spec_elem = function
  | SpecCV spec    -> pp_cvspec spec
(*  | SpecAttr attr  -> pp_attribute attr *)
  | SpecStorage st -> pp_storage st
  | SpecInline     -> pp_keyword "inline"
  | SpecType tSpec -> pp_typeSpecifier tSpec


and pp_decl_type = function
 | JUSTBASE ->
     fun z -> z
 | ARRAY (decl_t, specs, [], e_opt) ->
     fun z ->
       pp_decl_type decl_t z ^^
         P.brackets (
           P.separate_map P.space pp_cvspec specs ^^^
           P.optional (pp_expression None) e_opt
         )
 | PTR (specs, [], decl_t) ->
     fun z ->
       pp_decl_type decl_t $ P.parens (P.star ^^^ P.separate_map P.space pp_cvspec specs ^^^ z)



 | PROTO (decl_t, (params, is_va)) ->
     fun z->
       pp_decl_type decl_t z ^^
       P.parens (comma_list pp_parameter params ^^
                 if is_va then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                          else P.empty)


and pp_parameter (PARAM (spec_elems, str_opt, decl_t, [], _)) =
  P.separate_map P.space pp_spec_elem spec_elems ^^^
  pp_decl_type decl_t
    (P.optional P.string str_opt)


and pp_field_group (Field_group (spec_elems, xs, _)) =
  P.separate_map P.space pp_spec_elem spec_elems ^^^
  comma_list (function
    | (Some n, None)   -> pp_name n
    | (Some n, Some e) -> pp_name n ^^ P.colon ^^^ pp_expression None e
    | (None, Some e)   -> P.colon ^^^ pp_expression None e
  ) xs


and pp_name (Name (str, decl_t, [], _)) =
  pp_decl_type decl_t (!^ str)


and pp_init_name = function
  | Init_name (n, NO_INIT) -> pp_name n
  | Init_name (n, ie)      -> pp_name n ^^^ P.equals ^^^ pp_init_expression ie


and pp_binary_operator = function
  | ADD         -> P.plus
  | SUB         -> P.minus
  | MUL         -> P.star
  | DIV         -> P.slash
  | MOD         -> P.percent
  | AND         -> P.ampersand ^^ P.ampersand
  | OR          -> P.bar ^^ P.bar
  | BAND        -> P.ampersand
  | BOR         -> P.bar
  | XOR         -> P.caret
  | SHL         -> P.langle ^^ P.langle
  | SHR         -> P.rangle ^^ P.rangle
  | EQ          -> P.equals ^^ P.equals
  | NE          -> P.bang   ^^ P.equals
  | LT          -> P.langle
  | GT          -> P.rangle
  | LE          -> P.langle ^^ P.equals
  | GE          -> P.rangle ^^ P.equals
  | ASSIGN      -> P.equals
  | ADD_ASSIGN  -> P.equals ^^ P.plus
  | SUB_ASSIGN  -> P.equals ^^ P.minus
  | MUL_ASSIGN  -> P.equals ^^ P.star
  | DIV_ASSIGN  -> P.equals ^^ P.slash
  | MOD_ASSIGN  -> P.equals ^^ P.percent
  | BAND_ASSIGN -> P.equals ^^ P.ampersand
  | BOR_ASSIGN  -> P.equals ^^ P.bar
  | XOR_ASSIGN  -> P.equals ^^ P.caret
  | SHL_ASSIGN  -> P.equals ^^ P.langle ^^ P.langle
  | SHR_ASSIGN  -> P.equals ^^ P.rangle ^^ P.rangle
  | COMMA       -> P.comma


and pp_unary_operator = function
  | MINUS   -> P.minus
  | PLUS    -> P.plus
  | NOT     -> P.bang
  | BNOT    -> P.tilde
  | MEMOF   -> P.star
  | ADDROF  -> P.ampersand
  | PREINCR -> P.plus ^^ P.plus
  | PREDECR -> P.minus ^^ P.minus
  | POSINCR -> P.plus ^^ P.plus
  | POSDECR -> P.minus ^^ P.minus


and pp_expression p expr =
  let p' = precedence expr in
  let f = P.group -| pp_expression p' in
  (if lt_precedence p' p then fun x -> x else P.parens) $
    match expr with
      | UNARY (POSINCR as uop, e)
      | UNARY (POSDECR as uop, e) ->
          f e ^^ pp_unary_operator uop
      | UNARY (uop, e) ->
          pp_unary_operator uop ^^ f e
      | BINARY (bop, e1, e2) ->
          f e1 ^^^ pp_binary_operator bop ^^^ f e2
      | QUESTION (e1, e2, e3) ->
          P.group (f e1 ^^^ P.qmark ^/^ f e2 ^^^ P.colon ^/^ f e3)
      | CAST ((spec_elems, decl_t), ie) ->
          P.parens (pp_decl_type decl_t $ P.separate_map P.space pp_spec_elem spec_elems) ^^
          pp_init_expression ie
      
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
      
      | CALL (e, es) ->
          f e ^^ P.parens (comma_list f es)
(*  | BUILTIN_VA_ARG of expression * (list spec_elem * decl_type) *)
      | CONSTANT c ->
          pp_constant c
      | VARIABLE str ->
          !^ str
      | EXPR_SIZEOF e ->
          pp_keyword "sizeof" ^^^ f e
      | TYPE_SIZEOF (spec_elems, decl_t) ->
          pp_keyword "sizeof"  ^^
          P.parens (pp_decl_type decl_t $ P.separate_map P.space pp_spec_elem spec_elems)
      | ALIGNOF (spec_elems, decl_t) ->
          pp_keyword "_Alignof" ^^
          P.parens (pp_decl_type decl_t $ P.separate_map P.space pp_spec_elem spec_elems)
      | INDEX (e1 ,e2) ->
          f e1 ^^ P.brackets (f e2)
      | MEMBEROF (e, str) ->
          f e ^^ P.dot ^^ (!^ str)
      | MEMBEROFPTR (e, str) ->
          f e ^^ (!^ "->") ^^ (!^ str)
      | OFFSETOF ((spec_elems, decl_t), str) ->
          !^ "offsetof" ^^ P.parens (
            pp_decl_type decl_t $ P.separate_map P.space pp_spec_elem spec_elems ^^ P.comma ^^^
            !^ str
          )


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


(*
and pp_attribute (ATTR (str, es)) =
  assert false
*)


let pp_init_name_group (spec_elems, ins) =
  P.separate_map P.space pp_spec_elem spec_elems ^^^
  comma_list pp_init_name ins


let pp_name_group (spec_elems, ns) =
  P.separate_map P.space pp_spec_elem spec_elems ^^^
  P.separate_map P.space pp_name ns


let rec pp_definition = function
 | FUNDEF (spec_elems, n, s, _) ->
     P.separate_map P.space pp_spec_elem spec_elems ^^^
     pp_name n ^^^ pp_statement s
 | DECDEF (ing, _) ->
     pp_init_name_group ing
(* | PRAGMA (str, _) -> assert false *)


and pp_statement = function
 | NOP _ ->
     P.semi
 | COMPUTATION (e, _) ->
     pp_expression None e ^^ P.semi
 | BLOCK (ss, _) ->
     let block = P.separate_map (P.break 1) pp_statement ss in
     P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
 | If (e, s1, s2_opt, _) ->
     pp_keyword "if" ^^^ P.parens (pp_expression None e) ^^^ pp_statement s1 ^^
     P.optional (fun z -> P.space ^^ pp_keyword "else" ^^^ pp_statement z) s2_opt
 | WHILE (e, s, _) ->
     pp_keyword "while" ^^^ P.parens (pp_expression None e) ^/^ pp_statement s
 | DOWHILE (e, s, _) ->
     pp_keyword "do" ^/^ pp_statement s ^/^
       pp_keyword "while" ^^^ P.parens (pp_expression None e)
 | FOR (fc_opt, e2_opt, e3_opt, s, _) ->
     pp_keyword "for" ^^^
     P.parens (P.optional pp_for_clause fc_opt ^^ P.semi ^^^
               P.optional (pp_expression None) e2_opt ^^ P.semi ^^^
               P.optional (pp_expression None) e3_opt) ^/^ pp_statement s
 | BREAK _ ->
     pp_keyword "break" ^^ P.semi
 | CONTINUE _ ->
     pp_keyword "continue" ^^ P.semi
 | RETURN (e_opt, _) ->
     pp_keyword "return" ^^
     P.optional (fun z -> P.space ^^ pp_expression None z) e_opt ^^ P.semi
 | SWITCH (e, s, _) ->
     pp_keyword "switch" ^^^ P.parens (pp_expression None e) ^/^ pp_statement s
 | CASE (e, s, _) ->
     pp_expression None e ^^ P.colon ^^^ pp_statement s
 | DEFAULT (s, _) ->
     pp_keyword "default" ^^ P.colon ^^^ pp_statement s
 | LABEL (str, s, _) ->
     !^ str ^^ P.colon ^^^ pp_statement s
 | GOTO (str, _) ->
     pp_keyword "goto" ^^^ !^ str ^^ P.semi
 | DEFINITION def ->
     pp_definition def
 | PAR (ss, _) ->
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
