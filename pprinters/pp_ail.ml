open Global
open Ail

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | NULL
  | STRING_LITERAL _
  | VARIABLE _
  | CONSTANT _       -> Some 0
  
  | CALL _
  | MEMBEROF _
  | MEMBEROFPTR _
  | UNARY (POSTFIX_INCR, _)
  | UNARY (POSTFIX_DECR, _)
  | MALLOC _
  | FREE _
  | MEMCMP _
  | MEMCPY _
  | ASSERT _
  | CONST_ARRAY _
  | CONST_STRUCT_UNION _
  | OFFSETOF _              -> Some 1
  
  | UNARY _
  | CAST _
  | EXPR_SIZEOF _
  | SIZEOF _
  | ALIGNOF _     -> Some 2
  
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
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 < n2
    | (Some _ , None   ) -> true
    | (None   , _      ) -> false



let pp_id id = !^ (Symbol.to_string_pretty id)


let pp_storage_duration = function
  | STATIC    -> !^ "static"
  | THREAD    -> !^ "thread"
  | AUTOMATIC -> !^ "automatic"
  | ALLOCATED -> !^ "allocated"


let pp_cond switch str =
  if switch then
    !^ str
  else
    P.empty

let pp_qualifiers q =
  pp_cond q.const    "const"    ^^
  pp_cond q.restrict "restrict" ^^
  pp_cond q.volatile "volatile" ^^
  pp_cond q.atomic_q "atomic"


let pp_integer_base_type = function
  | ICHAR               -> !^ "char"
  | SHORT               -> !^ "short"
  | INT                 -> !^ "int"
  | LONG                -> !^ "long"
  | LONG_LONG           -> !^ "long" ^^^ !^ "long"
  | EXTENDED_INTEGER ty -> !^ ty


let pp_integer_type = function
  | BOOL        -> !^ "_Bool"
  | SIGNED   ib -> !^ "signed"   ^^^ pp_integer_base_type ib
  | UNSIGNED ib -> !^ "unsigned" ^^^ pp_integer_base_type ib


let pp_real_floating_type = function
  | FLOAT       -> !^ "float"
  | DOUBLE      -> !^ "double"
  | LONG_DOUBLE -> !^ "long" ^^^ !^ "double"


let pp_basic_type = function
  | CHAR             -> !^ "char"
  | INTEGER i        -> pp_integer_type i
  | REAL_FLOATING rf -> pp_real_floating_type rf
  | COMPLEX c        -> pp_real_floating_type c ^^^ !^ "_Complex"

let pp_integer = P.string -| Num.string_of_num

let rec pp_ctype t =
  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in
  match t with
    | VOID                    -> !^ "void"
    | BASIC  b                -> pp_basic_type b
    | ARRAY (qs, ty, n_opt)   -> pp_qualifiers qs ^^ pp_ctype ty ^^ P.brackets (P.optional pp_integer n_opt)
    | STRUCT (qs, tag, mems)  -> pp_qualifiers qs ^^ !^ "struct" ^^^ pp_id tag ^^^
                                 P.braces (pp_mems mems)
    | UNION (qs, tag, mems)   -> pp_qualifiers qs ^^ !^ "union" ^^^ pp_id tag ^^^
                                 P.braces (pp_mems mems)
    | ENUM name               -> !^ "enum" ^^^ pp_id name
    | FUNCTION (ty, ps)       -> pp_ctype ty ^^^
                                 P.parens (comma_list (fun (q,t) -> pp_qualifiers q ^^ pp_ctype t) ps)
    | POINTER (qs, ty)        -> pp_qualifiers qs ^^ pp_ctype ty ^^ P.star
    | ATOMIC ty               -> !^ "_Atomic" ^^^ pp_ctype ty
    | TYPEDEF name            -> pp_id name
    | SIZE_T                  -> !^ "size_t"
    | INTPTR_T                -> !^ "intptr_t"
    | WCHAR_T                 -> !^ "wchar_t"
    | CHAR16_T                -> !^ "char16_t"
    | CHAR32_T                -> !^ "char32_t"

and pp_member = function
  | MEMBER ty           -> fun z -> pp_ctype ty ^^^ pp_id z ^^ P.semi
  | BITFIELD (ty, w, _) -> fun z -> pp_ctype ty ^^^ pp_id z ^^ P.colon ^^^ pp_integer w ^^ P.semi


let pp_arithmetic_operator = function
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


let pp_binary_operator = function
  | ARITHMETIC o -> pp_arithmetic_operator o
  | COMMA        -> P.comma
  | AND          -> P.ampersand ^^ P.ampersand
  | OR           -> P.bar ^^ P.bar
  | LT           -> P.langle
  | GT           -> P.rangle
  | LE           -> P.langle ^^ P.equals
  | GE           -> P.rangle ^^ P.equals
  | EQ           -> P.equals ^^ P.equals
  | NE           -> P.bang   ^^ P.equals


let pp_unary_operator = function
  | PLUS         -> P.plus
  | MINUS        -> P.minus
  | BNOT         -> P.tilde
  | ADDRESS      -> P.ampersand
  | INDIRECTION  -> P.star
  | POSTFIX_INCR -> P.plus ^^ P.plus
  | POSTFIX_DECR -> P.minus ^^ P.minus


let pp_integer_suffix =
  let to_string = function
    | SUFFIX_UNSIGNED           -> "U"
    | SUFFIX_UNSIGNED_LONG      -> "UL"
    | SUFFIX_UNSIGNED_LONG_LONG -> "ULL"
    | SUFFIX_LONG               -> "L"
    | SUFFIX_LONG_LONG          -> "LL"
  in
  P.string -| to_string

(* TODO: should reverse the decoding of n *)
let pp_integer_constant (n, _, suff_opt) =
  !^ (Num.string_of_num n) ^^ (P.optional pp_integer_suffix suff_opt)


let pp_character_prefix =
  let to_string = function
    | PREFIX_L -> "L"
    | PREFIX_u -> "u"
    | PREFIX_U -> "U"
  in
  P.string -| to_string

let pp_character_constant (pref_opt, c) =
  (P.optional pp_character_prefix pref_opt) ^^ !^ (Num.string_of_num c)


let pp_constant = function
  | CONST_INT ic   -> pp_integer_constant ic
  | CONST_FLOAT fc -> !^ fc
  | CONST_CHAR cc  -> pp_character_constant cc
  | CONST_ENUM ec  -> !^ ec


let pp_encoding_prefix =
  let to_string = function
    | ENCODING_u8 -> "u8"
    | ENCODING_u  -> "u"
    | ENCODING_U  -> "U"
    | ENCODING_L  -> "L"
  in
  P.string -| to_string

let pp_string_literal (pref_opt, str) =
  (P.optional pp_encoding_prefix pref_opt) ^^ P.dquotes (!^ str)


let pp_expression_t expr_t =
  let rec pp p (_, expr) =
    let p' = precedence expr in
    let pp = P.group -| pp p' in
    (if lt_precedence p' p then fun z -> z else P.parens) $
      match expr with
        | NULL ->
            !^ "NULL"
        | STRING_LITERAL lit ->
            pp_string_literal lit
        | UNARY (POSTFIX_INCR as o, e)
        | UNARY (POSTFIX_DECR as o, e) ->
            pp e ^^ pp_unary_operator o
        | UNARY (o, e) ->
            pp_unary_operator o ^^ pp e
        | BINARY (COMMA as o, e1, e2) ->
            pp e1 ^^ pp_binary_operator o ^^ P.space ^^ pp e2
        | BINARY (o, e1, e2) ->
            pp e1 ^^^ pp_binary_operator o ^^^ pp e2
        | ASSIGN (o_opt, e1, e2) ->
            pp e1 ^^^ (P.optional pp_arithmetic_operator o_opt ^^ P.equals) ^^^ pp e2
        | CONDITIONAL (e1, e2, e3) ->
            P.group (pp e1 ^^^ P.qmark ^^^ pp e2 ^^^ P.colon ^^^ pp e3)
        | CAST (ty, e) ->
            P.parens (pp_ctype ty) ^^^ pp e
        | CALL (e, es) ->
            pp e ^^ P.parens (comma_list pp es)
        | MEMBEROF (e, (tag, mem)) ->
            pp e ^^ P.dot ^^ pp_id mem
        | MEMBEROFPTR (e, (tag, mem)) ->
            pp e ^^ (!^ "->") ^^ pp_id mem
        | CONSTANT c ->
            pp_constant c
        | VARIABLE x ->
            pp_id x
        | EXPR_SIZEOF e ->
            !^ "sizeof" ^^^ pp e
        | SIZEOF ty ->
            !^ "sizeof" ^^ P.parens (pp_ctype ty)
        | ALIGNOF ty ->
            !^ "_Alignof" ^^ P.parens (pp_ctype ty)
        | MALLOC e ->
            !^ "malloc" ^^ P.parens (pp e)
        | FREE e ->
            !^ "free" ^^ P.parens (pp e)
        | MEMCMP (e1, e2, e3) ->
            !^ "memcmp" ^^ P.parens (pp e1 ^^ P.comma ^^^ pp e2 ^^ P.comma ^^^ pp e3)
        | MEMCPY (e1, e2, e3) ->
            !^ "memcpy" ^^ P.parens (pp e1 ^^ P.comma ^^^ pp e2 ^^ P.comma ^^^ pp e3)
        | ASSERT e ->
            !^ "assert" ^^ P.parens (pp e)
        | CONST_ARRAY es ->
            P.braces (comma_list pp es)
        | CONST_STRUCT_UNION mems ->
            P.braces (comma_list (fun (mem, e) -> pp_id mem ^^ P.equals ^^^ pp e) mems)
        | OFFSETOF (ty, mem) ->
            !^ "offsetof" ^^ P.parens (pp_ctype ty ^^ P.comma ^^^ pp_id mem)
        | PRINTF (e1, es) ->
            !^ "printf" ^^ P.parens (pp e1 ^^ P.comma ^^^ comma_list pp es)
  in
  pp None expr_t


let pp_definition file (name, e) = 
  let (ty, _) = Pmap.find name file.id_map in
  pp_ctype ty ^^^ pp_id name ^^^ P.equals ^^^ pp_expression_t e


let rec pp_statement_l file (_, stmt) =
  let pp_statement_l = pp_statement_l file in
(*
  let nest' (_, stmt) =
    match stmt with
      | BLOCK _ -> 
*)
  match stmt with
    | SKIP ->
        P.semi
    | EXPRESSION e ->
        pp_expression_t e ^^ P.semi
    | BLOCK (ids, ss) -> (* TODO: decls *)
        let block = P.separate_map (P.break 1) pp_statement_l ss in
        !^ "BLOCK_VARS" ^^^ comma_list pp_id ids ^^^
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
    | IF (e, s1, s2) ->
        !^ "if" ^^^ P.parens (pp_expression_t e) ^/^
          P.nest 2 (pp_statement_l s1) ^^^
        !^ "else" ^/^
          pp_statement_l s2
    | WHILE (e, s) ->
        !^ "while" ^^^ P.parens (pp_expression_t e) ^^^ pp_statement_l s
    | DO (e, s) ->
        !^ "do" ^^^ pp_statement_l s ^^^ !^ "while" ^^^ P.parens (pp_expression_t e)
    | BREAK ->
        !^ "break" ^^ P.semi
    | CONTINUE ->
        !^ "continue" ^^ P.semi
    | RETURN_VOID ->
        !^ "return" ^^ P.semi
    | RETURN_EXPRESSION e ->
        !^ "return" ^^^ pp_expression_t e ^^ P.semi
    | SWITCH (e, s) ->
        !^ "switch" ^^^ P.parens (pp_expression_t e) ^/^ pp_statement_l s
    | CASE (ic, s) ->
        pp_integer_constant ic ^^ P.colon ^/^ pp_statement_l s
    | DEFAULT s ->
        !^ "default" ^^ P.colon ^/^ pp_statement_l s
    | LABEL (l, s) ->
        pp_id l ^^ P.colon ^/^ pp_statement_l s
    | GOTO l ->
        !^ "goto" ^^^ pp_id l ^^ P.semi
    | DECLARATION defs ->
        comma_list (pp_definition file) defs ^^ P.semi
    | PAR ss ->
        (P.lbrace ^^ P.lbrace ^^ P.lbrace) ^/^
        (P.nest 2 (P.break 1 ^^ P.separate_map (P.bar ^^ P.bar ^^ P.bar) pp_statement_l ss)) ^/^
        (P.rbrace ^^ P.rbrace ^^ P.rbrace)


let pp_declaration file name =
  let (ty, _) = Pmap.find name file.id_map in
  pp_ctype ty ^^^ pp_id name


let pp_function file (id, (args, s)) =
  let (ty, st) = Pmap.find id file.id_map in
  (match ty with
    | FUNCTION (ret_ty, _) -> pp_ctype ret_ty
    | _                    -> P.empty
  )
  ^^^ pp_id id
  ^^^ P.parens (comma_list (pp_declaration file) args)
  ^^^ (pp_statement_l file s)


let pp_file file =
  let pp d f = d ^^ pp_function file f ^^ P.break 1 in
(*  (List.fold_left (fun (name, (ty, _)) -> pp_ctype ty ^^^ pp_id name) P.empty (Pmap.bindings file.id_map)) ^^^ *)
  (List.fold_left pp P.empty (Pmap.bindings file.fn_map))

