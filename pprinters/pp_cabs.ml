open Global
open Cabs

open Colour

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | IDENTIFIER _
  | CONSTANT _
  | STRING_LITERAL _
  | GENERIC_SELECTION _
  | OFFSETOF _ -> Some 0
  
  | SUBSCRIPT _
  | CALL _
  | MEMBEROF _
  | MEMBEROFPTR _
  | UNARY (POSTFIX_INCR, _)
  | UNARY (POSTFIX_DECR, _) -> Some 1
  
  | UNARY _
  | CAST _
  | EXPR_SIZEOF _
  | TYPE_SIZEOF _
  | TYPE_ALIGNOF _ -> Some 2
  
  | BINARY (ARITHMETIC MUL, _, _)
  | BINARY (ARITHMETIC DIV, _, _)
  | BINARY (ARITHMETIC MOD, _, _) -> Some 3
  
  | BINARY (ARITHMETIC ADD, _, _)
  | BINARY (ARITHMETIC SUB, _, _) -> Some 4
  
  | BINARY (ARITHMETIC SHL, _, _)
  | BINARY (ARITHMETIC SHR, _, _) -> Some 5
  
  | BINARY (LT, _, _)
  | BINARY (GT, _, _)
  | BINARY (LE, _, _)
  | BINARY (GE, _, _) -> Some 6
  
  | BINARY (EQ, _, _)
  | BINARY (NE, _, _) -> Some 7
  
  | BINARY (ARITHMETIC BAND, _, _) -> Some 8
  
  | BINARY (ARITHMETIC XOR, _, _) -> Some 9
  
  | BINARY (ARITHMETIC BOR, _, _) -> Some 10
  
  | BINARY (AND, _, _) -> Some 11
  
  | BINARY (OR, _, _) -> Some 12
  
  | CONDITIONAL _ -> Some 13
  
  | ASSIGN _ -> Some 14
  
  | BINARY (COMMA, _, _) -> Some 15


let lt_precedence p1 p2 =
  match p1, p2 with
    | Some n1, Some n2 -> n1 < n2
    | Some _ , None    -> true
    | None   , _       -> false


let pp_integer_suffix s =
  let to_string = function
    | SUFFIX_UNSIGNED           -> "U"
    | SUFFIX_UNSIGNED_LONG      -> "UL"
    | SUFFIX_UNSIGNED_LONG_LONG -> "ULL"
    | SUFFIX_LONG               -> "L"
    | SUFFIX_LONG_LONG          -> "LL"
  in
  P.optional (P.string -| to_string) s
let pp_integer_constant (i, s) = !^ i ^^ pp_integer_suffix s


let pp_character_prefix p =
  let to_string = function
    | PREFIX_L -> "L"
    | PREFIX_u -> "u"
    | PREFIX_U -> "U"
  in
  P.optional (P.string -| to_string) p
let pp_character_constant (p, c) = pp_character_prefix p ^^ P.squotes (!^ c)

let pp_encoding_prefix = function
  | ENCODING_u8 -> !^ "u8"
  | ENCODING_u  -> !^ "u"
  | ENCODING_U  -> !^ "U"
  | ENCODING_L  -> !^ "L"
let pp_string_literal (enc, s) =
  (P.optional pp_encoding_prefix enc) ^^ (!^ s)


let pp_arithop = function
  | MUL  -> P.star
  | DIV  -> P.slash
  | MOD  -> P.percent
  | ADD  -> P.plus
  | SUB  -> P.minus
  | SHL  -> P.langle ^^ P.langle
  | SHR  -> P.rangle ^^ P.rangle
  | BAND -> P.ampersand
  | BOR  -> P.bar
  | XOR  -> P.caret


let pp_binop = function
  | ARITHMETIC op -> pp_arithop op
  | COMMA         -> P.comma
  | AND           -> P.ampersand ^^ P.ampersand
  | OR            -> P.bar ^^ P.bar
  | LT            -> P.langle
  | GT            -> P.rangle
  | LE            -> P.langle ^^ P.equals
  | GE            -> P.rangle ^^ P.equals
  | EQ            -> P.equals ^^ P.equals
  | NE            -> P.bang   ^^ P.equals


let pp_unop = function
  | POSTFIX_INCR -> P.plus ^^ P.plus
  | POSTFIX_DECR -> P.minus ^^ P.minus
  | PREFIX_INCR  -> P.plus ^^ P.plus
  | PREFIX_DECR  -> P.minus ^^ P.minus
  | ADDRESS      -> P.ampersand
  | INDIRECTION  -> P.star
  | PLUS         -> P.plus
  | MINUS        -> P.minus
  | BNOT         -> P.tilde
  | NOT          -> P.bang


let pp_storage_class = function
  | TYPEDEF      -> !^ (ansi_format [Cyan; Bold] "typedef")
  | EXTERN       -> !^ (ansi_format [Cyan; Bold] "extern")
  | STATIC       -> !^ (ansi_format [Cyan; Bold] "static")
  | THREAD_LOCAL -> !^ (ansi_format [Cyan; Bold] "_Thread_Local")
  | AUTO         -> !^ (ansi_format [Cyan; Bold] "auto")
  | REGISTER     -> !^ (ansi_format [Cyan; Bold] "register")


let pp_qualifier = function
  | CONST    -> !^ (ansi_format [Cyan; Bold] "const")
  | RESTRICT -> !^ (ansi_format [Cyan; Bold] "restrict")
  | VOLATILE -> !^ (ansi_format [Cyan; Bold] "volatile")
  | ATOMIC_Q -> !^ (ansi_format [Cyan; Bold] "_Atomic")


let rec pp_specifier = function
  | VOID      -> !^ (ansi_format [Green] "void")
  | CHAR      -> !^ (ansi_format [Green] "char")
  | SHORT     -> !^ (ansi_format [Green] "short")
  | INT       -> !^ (ansi_format [Green] "int")
  | LONG      -> !^ (ansi_format [Green] "long")
  | FLOAT     -> !^ (ansi_format [Green] "float")
  | DOUBLE    -> !^ (ansi_format [Green] "double")
  | SIGNED    -> !^ (ansi_format [Green] "signed")
  | UNSIGNED  -> !^ (ansi_format [Green] "unsigned")
  | BOOL      -> !^ (ansi_format [Green] "_Bool")
  | COMPLEX   -> !^ (ansi_format [Green] "_Complex")
  | NAMED ty  -> !^ (ansi_format [Green] ty)
  | ATOMIC ty -> !^ (ansi_format [Green] "_Atomic") ^^ P.parens (pp_type ty)
  (* TODO: attributes *)
  | STRUCT (tag_opt, fs, attrs) ->
      !^ (ansi_format [Cyan; Bold] "struct") ^^
      (P.optional (fun z -> P.space ^^ !^ (ansi_format [Green] z)) tag_opt) ^^^
      P.braces (comma_list pp_field fs)

  | UNION (tag_opt, fs, attrs) ->
      !^ (ansi_format [Cyan; Bold] "union") ^^
      (P.optional (fun z -> P.space ^^  !^ (ansi_format [Green] z)) tag_opt)
(*    | ENUM of option string * option (list (string * option exp_l)) * list attribute *)
  | _ -> !^ "TODO_pp_specifier"


(*
    | STRUCT (name_opt, decls) ->
        !^ (ansi_format [Green] "struct") ^^
          match decls with
            | []    -> P.empty
            | delcs -> P.lbrace ^^ P.nest 2 (P.break 1 ^^
                                               let f ds d = ds ^^ d ^^ P.hardline in
                                               P.sepmap P.break0 pp_struct_union_declaration decls) ^/^ P.rbrace
*)

and pp_field = function
  | BasicField (n, ty)      -> pp_type ty ^^^ (!^ n)
  | BitField (n_opt, ty, e) -> pp_type ty ^^^ (P.optional (!^) n_opt) ^^^ P.colon ^^ (pp_exp None e)


and pp_type = function
  | BASE (_, ss) ->
      pp_ss ss
  | ARRAY (_, ty, e_opt) -> 
      !^ "array " ^^^ (P.optional (pp_exp None) e_opt) ^^^ !^ "of" ^^^ pp_type ty
  | POINTER (_, ty) ->
      !^ "pointer to" ^^^ pp_type ty
  | FUNCTION (ty, ds) ->
      !^ "function" ^^^ P.parens (comma_list (fun ((_, ty, _), _) -> pp_type ty) ds) ^^^
      !^ "returning" ^^^ pp_type ty


(*

  | BASE (qs, ss)     -> pp_qs qs ^^ pp_ss ss
  | ARRAY (qs, ty, e_opt) -> 
    !^ "array " ^^^ (P.optional (pp_exp None) e_opt) ^^^ !^ "of" ^^^ P.parens (pp_type ty)


(* pp_qs qs ^^ pp_type ty ^^^ P.brackets (match e with
                                                                       | Some e -> pp_exp None e
                                                                       | None   -> P.empty) *)
(*                         !^ "BOOM" *)
  | POINTER (qs, ty)  -> pp_qs qs ^^^ P.parens (pp_type ty) ^^^ P.star
  | FUNCTION (ty, ds) -> pp_type ty ^^ P.parens (!^ "TODO") (* (P.comma_list f ts) *) (* TODO *)
*)


and pp_exp p (exp, _) =
  let p' = precedence exp in
  let f = P.group -| pp_exp p' in
  (if lt_precedence p' p then fun x -> x else P.parens) $
    match exp with
      | IDENTIFIER id                 -> !^ id
      | CONSTANT (CONST_INT ic)       -> pp_integer_constant ic
      | CONSTANT (CONST_FLOAT fc)     -> !^ fc
      | CONSTANT (CONST_CHAR cc)      -> pp_character_constant cc
      | STRING_LITERAL s              -> pp_string_literal s (* TODO: should put braces when cabs_transform does an actual translation of the string *)
      | SUBSCRIPT (e1, e2)            -> f e1 ^^ P.brackets (f e2)
      | CALL (e, es)                  -> f e ^^ P.parens (comma_list f es)
      | MEMBEROF (e, x)               -> f e ^^ P.dot ^^ (!^ x)
      | MEMBEROFPTR (e,x)             -> f e ^^ (!^ "->") ^^ (!^ x)
      | UNARY (POSTFIX_INCR as op, e) -> f e ^^ pp_unop op
      | UNARY (POSTFIX_DECR as op, e) -> f e ^^ pp_unop op
      | UNARY (op, e)                 -> pp_unop op ^^ f e
      | EXPR_SIZEOF e                 -> !^ "sizeof"  ^^^ f e
      | TYPE_SIZEOF ty                -> !^ "sizeof"  ^^ P.parens (pp_type ty)
      | TYPE_ALIGNOF ty               -> !^ "alignof" ^^ P.parens (pp_type ty)
      | CAST (ty, e)                  -> P.parens (pp_type ty) ^^^ f e
      | BINARY (COMMA as op, e1, e2)  -> f e1 ^^ pp_binop op ^^ P.space ^^ f e2
      | BINARY (op, e1, e2)           -> f e1 ^^^ pp_binop op ^^^ f e2
      | CONDITIONAL (e1, e2, e3)      -> P.group (f e1 ^^^ P.qmark ^/^ f e2 ^^^ P.colon ^/^ f e3)
      | ASSIGN (op_opt, e1, e2)       -> f e1 ^^^ (P.optional pp_arithop op_opt ^^ P.equals) ^^^ f e2
      | OFFSETOF (ty, s)              -> !^ "offsetof" ^^ P.parens (pp_type ty ^^ P.comma ^^^ (!^ s))


and ins_space ds d = ds ^^ d ^^ P.space
and pp_qs qs =
  List.fold_right ins_space (List.map pp_qualifier (Pset.elements qs)) P.empty
and pp_ss ss =
  let rec replicate x = function
    | 0    -> P.empty
    | n    -> pp_specifier x ^^^ replicate x (n-1) in
  List.fold_right ins_space (List.map (fun (x,n) -> replicate x n) (Pmap.bindings ss)) P.empty
  
  









      


(*
  and pp_id id = !^ (Symbol.to_string_pretty id)

  let pp_decl file id =
    let (t, st) = Pmap.find id file.id_map in
    pp_type t ^^^ pp_id id
*)

  let rec pp_stmt (stmt, _) =
    match stmt with
      | SKIP                                -> P.semi
      | LABEL (id, s)                       -> !^ id ^^ P.colon ^^^ pp_stmt s
      | CASE (e, s)                         -> pp_exp None e ^^ P.colon ^^^ pp_stmt s
      | DEFAULT s                           -> !^ "default" ^^ P.colon ^^^ pp_stmt s
      | BLOCK ss                            -> let block = P.separate_map (P.break 1) pp_stmt ss in
                                               P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
      | EXPRESSION e                        -> pp_exp None e ^^ P.semi
      | IF (e, s1, Some s2)                 -> !^ (ansi_format [Cyan; Bold] "if") ^^^ P.parens (pp_exp None e) ^^^
                                               pp_stmt s1 ^^^ !^ (ansi_format [Cyan; Bold] "else") ^^^
                                               pp_stmt s2
      | IF (e, s1, None)                    -> !^ (ansi_format [Cyan; Bold] "if") ^^^ P.parens (pp_exp None e) ^^^
                                               pp_stmt s1
      | SWITCH (e, s)                       -> !^ (ansi_format [Cyan; Bold] "switch") ^^^
                                               P.parens (pp_exp None e) ^/^ pp_stmt s
      | WHILE (e, s)                        -> !^ (ansi_format [Cyan; Bold] "while") ^^^
                                               P.parens (pp_exp None e) ^/^ pp_stmt s
      | DO (e, s)                           -> !^ (ansi_format [Cyan; Bold] "do") ^/^ pp_stmt s ^/^
                                               !^ (ansi_format [Cyan; Bold] "while") ^^^ P.parens (pp_exp None e)
      | FOR_EXP (e1_opt, e2_opt, e3_opt, s) -> !^ (ansi_format [Cyan; Bold] "for") ^^
                                               P.parens (P.optional (pp_exp None) e1_opt ^^ P.semi ^^^
                                                         P.optional (pp_exp None) e2_opt ^^ P.semi ^^^
                                                         P.optional (pp_exp None) e3_opt) ^/^ pp_stmt s
      | FOR_DECL (defs, e1_opt, e2_opt, s)  -> !^ "for" (* TODO *)
      | GOTO id                             -> !^ (ansi_format [Cyan; Bold] "goto") ^^^ !^ id ^^ P.semi
      | CONTINUE                            -> !^ (ansi_format [Cyan; Bold] "continue") ^^ P.semi
      | BREAK                               -> !^ (ansi_format [Cyan; Bold] "break") ^^ P.semi
      | RETURN (Some e)                     -> !^ (ansi_format [Cyan; Bold] "return") ^^^ pp_exp None e ^^ P.semi
      | RETURN None                         -> !^ (ansi_format [Cyan; Bold] "return") ^^ P.semi
      | DECLARATION defs                    -> comma_list pp_definition defs ^^ P.semi
      | PAR ss                              -> let par = P.separate_map (P.bar ^^ P.bar ^^ P.bar) pp_stmt ss in
                                               P.lbrace ^^ P.lbrace ^^ P.lbrace ^^ P.nest 2 (P.break 1 ^^ par) ^/^ P.rbrace ^^ P.rbrace ^^ P.rbrace
  
  and pp_declaration ((str, ty, scs), _) =
    !^ "declare" ^^^ !^ str ^^^ !^ "as" ^^^ pp_type ty

(*
    List.fold_right ins_space (List.map pp_storage_class scs) P.empty ^^
    (match ty with
      | ARRAY (qs, ty, e) -> pp_qs qs ^^ pp_type ty ^^^ (!^ s) ^^
                             P.brackets (match e with Some e -> pp_exp None e | None -> P.empty)
      | FUNCTION (ty, decls) ->
        Printf.printf "> %d\n" (List.length decls);

        
pp_type ty ^^ !^ (ansi_format [Blue] s) ^^
                                P.parens (comma_list pp_declaration decls)
      | ty                   -> pp_type ty ^^ !^ (ansi_format [Yellow] s))
*)
    
  
  and pp_init_exp = function
    | SINGLE_INIT exp  -> pp_exp None exp
    | ARRAY_INIT inits -> P.braces $ (comma_list pp_init_exp) inits
  
  and pp_definition = function
    | (TYPE_DEF ty, _) -> pp_type ty
    | (OTHER_DEF (decl, init_opt), _) ->
        pp_declaration decl ^^^
          (match init_opt with
            | Some init -> P.equals ^^^ pp_init_exp init
            | None      -> P.empty)
  
  let pp_global_definition (def, _) =
    match def with
      | FUNCTION_DEFINITION (decl, stmt) -> pp_declaration decl ^^^ pp_stmt stmt
      | EXTERNAL_DECLARATION (decls)     -> List.fold_right ins_space (List.map pp_definition decls) P.empty
                                              
  let pp_file defs =
    let pp d def = d ^^ pp_global_definition def ^^ P.break 1 in
    List.fold_left pp P.empty defs
