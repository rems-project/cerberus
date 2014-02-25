open Lem_pervasives
open Either

open Global
open AilSyntax
open AilTypes


module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
(*
  | NULL
  | STRING_LITERAL _
*)
  | Var _
  | Constant _       -> Some 0
  
  | Call _
(*
  | MEMBEROF _
  | MEMBEROFPTR _
*)
  | Unary (PostfixIncr, _)
  | Unary (PostfixDecr, _)  -> Some 1
(*
  | MALLOC _
  | FREE _
  | MEMCMP _
  | MEMCPY _
  | ASSERT _
  | CONST_ARRAY _
  | CONST_STRUCT_UNION _
  | OFFSETOF _              -> Some 1
*)
  
  | Unary _
  | Cast _
(*  | EXPR_SIZEOF _ *)
  | SizeOf _
  | AlignOf _     -> Some 2
  
  | Binary (_, Arithmetic Mul, _)
  | Binary (_, Arithmetic Div, _)
  | Binary (_, Arithmetic Mod, _) -> Some 3
  
  | Binary (_, Arithmetic Add, _)
  | Binary (_, Arithmetic Sub, _) -> Some 4
  
  | Binary (_, Arithmetic Shl, _)
  | Binary (_, Arithmetic Shr, _) -> Some 5
  
  | Binary (_, Lt, _)
  | Binary (_, Gt, _)
  | Binary (_, Le, _)
  | Binary (_, Ge, _) -> Some 6
  
  | Binary (_, Eq, _)
  | Binary (_, Ne, _) -> Some 7
  
  | Binary (_, Arithmetic Band, _) -> Some 8
  
  | Binary (_, Arithmetic Xor, _) -> Some 9
  
  | Binary (_, Arithmetic Bor, _) -> Some 10
  
  | Binary (_, And, _) -> Some 11
  
  | Binary (_, Or, _) -> Some 12
  
  | Conditional _ -> Some 13
  
  | Assign _
  | CompoundAssign _ -> Some 14
  
  | Binary (_, Comma, _) -> Some 15


let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 < n2
    | (Some _ , None   ) -> true
    | (None   , _      ) -> false



let pp_id id = !^ (Pp_symbol.to_string_pretty id)


let pp_storageDuration = function
  | Static    -> !^ "static"
  | Thread    -> !^ "thread"
  | Automatic -> !^ "automatic"
  | Allocated -> !^ "allocated"


let pp_cond switch str =
  if switch then
    (^^^) !^ str
  else
    (^^) P.empty

let pp_qualifiers q =
  fun z ->
    pp_cond q.const    "const"
      (pp_cond q.restrict "restrict"
         (pp_cond q.volatile "volatile" z)
      )
(*
  pp_cond q.atomic_q "atomic"
*)


let pp_integerBaseType = function
 | Ichar    -> !^ "char"
 | Short    -> !^ "short"
 | Int_     -> !^ "int"
 | Long     -> !^ "long"
 | LongLong -> !^ "long" ^^^ !^ "long"


let pp_integerType = function
 | Char             -> !^ "char"
 | Bool             -> !^ "_Bool"
 | Signed Int8_t    -> !^ "int8_t"
 | Signed Int16_t   -> !^ "int16_t"
 | Signed Int32_t   -> !^ "int32_t"
 | Signed Int64_t   -> !^ "int64_t"
 | Unsigned Int8_t  -> !^ "uint8_t"
 | Unsigned Int16_t -> !^ "uint16_t"
 | Unsigned Int32_t -> !^ "uint32_t"
 | Unsigned Int64_t -> !^ "uint64_t"
 | Signed ibt       -> !^ "signed"   ^^^ pp_integerBaseType ibt
 | Unsigned ibt     -> !^ "unsigned" ^^^ pp_integerBaseType ibt


(*
let pp_real_floating_type = function
  | FLOAT       -> !^ "float"
  | DOUBLE      -> !^ "double"
  | LONG_DOUBLE -> !^ "long" ^^^ !^ "double"
*)


let pp_basicType = function
  | Integer it -> pp_integerType it



let pp_integer i = P.string (Big_int.string_of_big_int i)

let rec pp_ctype t =
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  match t with
    | Void ->
        !^ "void"
    | Basic  b ->
        pp_basicType b
    | Array (ty, n) ->
        pp_ctype ty ^^ P.brackets (pp_integer n)
    | Function (ty, ps, is_variadic) ->
        pp_ctype ty ^^^ P.parens (comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype t)) ps ^^ (if is_variadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty))
    | Pointer (qs, ty) ->
        pp_qualifiers qs (pp_ctype ty) ^^ P.star
    | Atomic ty ->
        !^ "_Atomic" ^^^ pp_ctype ty
(*
    | STRUCT (qs, tag, mems)  -> pp_qualifiers qs ^^ !^ "struct" ^^^ pp_id tag ^^^
                                 P.braces (pp_mems mems)
    | UNION (qs, tag, mems)   -> pp_qualifiers qs ^^ !^ "union" ^^^ pp_id tag ^^^
                                 P.braces (pp_mems mems)
    | ENUM name               -> !^ "enum" ^^^ pp_id name
*)
(*
    | TYPEDEF name            -> pp_id name
    | SIZE_T                  -> !^ "size_t"
    | INTPTR_T                -> !^ "intptr_t"
    | WCHAR_T                 -> !^ "wchar_t"
    | CHAR16_T                -> !^ "char16_t"
    | CHAR32_T                -> !^ "char32_t"
*)

(*
and pp_member = function
  | MEMBER ty           -> fun z -> pp_ctype ty ^^^ pp_id z ^^ P.semi
  | BITFIELD (ty, w, _) -> fun z -> pp_ctype ty ^^^ pp_id z ^^ P.colon ^^^ pp_integer w ^^ P.semi
*)


let pp_arithmeticOperator = function
  | Mul  -> P.star
  | Div  -> P.slash
  | Mod  -> P.percent
  | Add  -> P.plus
  | Sub  -> P.minus
  | Shl  -> P.langle ^^ P.langle
  | Shr  -> P.rangle ^^ P.rangle
  | Band -> P.ampersand
  | Bor  -> P.bar
  | Xor  -> P.caret


let pp_binaryOperator = function
  | Arithmetic o -> pp_arithmeticOperator o
  | Comma        -> P.comma
  | And          -> P.ampersand ^^ P.ampersand
  | Or           -> P.bar ^^ P.bar
  | Lt           -> P.langle
  | Gt           -> P.rangle
  | Le           -> P.langle ^^ P.equals
  | Ge           -> P.rangle ^^ P.equals
  | Eq           -> P.equals ^^ P.equals
  | Ne           -> P.bang   ^^ P.equals


let pp_unaryOperator = function
  | Plus        -> P.plus
  | Minus       -> P.minus
  | Bnot        -> P.tilde
  | Address0    -> P.ampersand
  | Indirection -> P.star
  | PostfixIncr -> P.plus ^^ P.plus
  | PostfixDecr -> P.minus ^^ P.minus


let pp_integerSuffix =
  let to_string = function
    | U   -> "U"
    | UL  -> "UL"
    | ULL -> "ULL"
    | L   -> "L"
    | LL  -> "LL"
  in
  fun z -> P.string (to_string z)

(* TODO: should reverse the decoding of n *)
let pp_integerConstant (n, suff_opt) =
  !^ (Big_int.string_of_big_int n) ^^ (P.optional pp_integerSuffix suff_opt)


(*
let pp_character_prefix =
  let to_string = function
    | PREFIX_L -> "L"
    | PREFIX_u -> "u"
    | PREFIX_U -> "U"
  in
  P.string -| to_string

let pp_character_constant (pref_opt, c) =
  (P.optional pp_character_prefix pref_opt) ^^ !^ (Num.string_of_num c)
*)


let pp_constant = function
  | ConstantInteger ic -> pp_integerConstant ic
  | ConstantString str -> !^ str
(*
  | CONST_FLOAT fc -> !^ fc
  | CONST_CHAR cc  -> pp_character_constant cc
  | CONST_ENUM ec  -> !^ ec
*)


(*
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
*)


let pp_expression a_expr =
  let rec pp p (AnnotatedExpression (_, expr)) =
    let p' = precedence expr in
    let pp z = P.group (pp p' z) in
    (if lt_precedence p' p then fun z -> z else P.parens)
      (match expr with
(*
        | STRING_LITERAL lit ->
            pp_string_literal lit
*)
        | Unary (PostfixIncr as o, e)
        | Unary (PostfixDecr as o, e) ->
            pp e ^^ pp_unaryOperator o
        | Unary (o, e) ->
            pp_unaryOperator o ^^ pp e
        | Binary (e1, (Comma as o), e2) ->
            pp e1 ^^ pp_binaryOperator o ^^ P.space ^^ pp e2
        | Binary (e1, o, e2) ->
            pp e1 ^^^ pp_binaryOperator o ^^^ pp e2
        | Assign (e1, e2) ->
            pp e1 ^^^ P.equals ^^^ pp e2
        | CompoundAssign (e1, o, e2) ->
            pp e1 ^^^ pp_arithmeticOperator o ^^ P.equals ^^^ pp e2
        | Conditional (e1, e2, e3) ->
            P.group (pp e1 ^^^ P.qmark ^^^ pp e2 ^^^ P.colon ^^^ pp e3)
        | Cast (qs, ty, e) ->
            pp_qualifiers qs (P.parens (pp_ctype ty)) ^^^ pp e
        | Call (e, es) ->
            pp e ^^ P.parens (comma_list pp es)
        | Constant c ->
            pp_constant c
        | Var x ->
            pp_id x
        | SizeOf (qs, ty) ->
            !^ "sizeof" ^^ P.parens (pp_qualifiers qs (pp_ctype ty))
        | AlignOf (qs, ty) ->
            !^ "_Alignof" ^^ P.parens (pp_qualifiers qs (pp_ctype ty))


(*
        | MEMBEROF (e, (tag, mem)) ->
            pp e ^^ P.dot ^^ pp_id mem
        | MEMBEROFPTR (e, (tag, mem)) ->
            pp e ^^ (!^ "->") ^^ pp_id mem
        | EXPR_SIZEOF e ->
            !^ "sizeof" ^^^ pp e
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
*)
      )
  in
  pp None a_expr


(*
let pp_definition file (name, e) = 
  let (ty, _) = Pmap.find name file.id_map in
  pp_ctype ty ^^^ pp_id name ^^^ P.equals ^^^ pp_expression_t e
*)

(*
let pp_typed_id file name =
  let (q, t, _) = Pmap.find name file.id_map in
  pp_id name ^^ P.colon ^^^ (pp_qualifiers q $ pp_ctype t)
*)

let rec pp_statement (AnnotatedStatement (_, stmt)) =
  let pp_statement = pp_statement in
(*
  let nest' (_, stmt) =
    match stmt with
      | BLOCK _ -> 
*)
  match stmt with
    | Skip ->
        P.semi
    | Expression e ->
        pp_expression e ^^ P.semi
    | Block (ids, ss) ->
        let block =
          P.separate_map
            (P.semi ^^ P.break 1)
            (fun (id, (qs, ty)) -> pp_qualifiers qs (pp_ctype ty) ^^^ pp_id id)
            ids ^^
          P.break 1 ^^
          P.separate_map (P.break 1) pp_statement ss in
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
    | If (e, s1, s2) ->
        !^ "if" ^^^ P.parens (pp_expression e) ^/^
          P.nest 2 (pp_statement s1) ^^^
        !^ "else" ^/^
          pp_statement s2
    | While (e, s) ->
        !^ "while" ^^^ P.parens (pp_expression e) ^^^ pp_statement s
    | Do (s, e) ->
        !^ "do" ^^^ pp_statement s ^^^ !^ "while" ^^^ P.parens (pp_expression e)
    | Break ->
        !^ "break" ^^ P.semi
    | Continue ->
        !^ "continue" ^^ P.semi
    | ReturnVoid ->
        !^ "return" ^^ P.semi
    | Return e ->
        !^ "return" ^^^ pp_expression e ^^ P.semi
    | Switch (e, s) ->
        !^ "switch" ^^^ P.parens (pp_expression e) ^/^ pp_statement s
    | Case (ic, s) ->
        pp_integerConstant ic ^^ P.colon ^/^ pp_statement s
    | Default s ->
        !^ "default" ^^ P.colon ^/^ pp_statement s
    | Label (l, s) ->
        pp_id l ^^ P.colon ^/^ pp_statement s
    | Goto l ->
        !^ "goto" ^^^ pp_id l ^^ P.semi
    (* TODO: looks odd *)
    | Declaration defs ->
        comma_list (fun (id, e) -> pp_id id ^^^ P.equals ^^^ pp_expression e) defs ^^
        P.semi
(*
    | PAR ss ->
        (P.lbrace ^^ P.lbrace ^^ P.lbrace) ^/^
        (P.nest 2 (P.break 1 ^^ P.separate_map (P.bar ^^ P.bar ^^ P.bar) pp_statement_l ss)) ^/^
        (P.rbrace ^^ P.rbrace ^^ P.rbrace)
*)

(*
let pp_declaration file name =
  let (q, ty, _) = Pmap.find name file.id_map in
  (pp_qualifiers q $ pp_ctype ty) ^^^ pp_id name


let pp_function file (id, (args, s)) =
  let (_, ty, st) = Pmap.find id file.id_map in
  (match ty with
    | FUNCTION (ret_ty, _) -> pp_ctype ret_ty
    | _                    -> P.empty
  )
  ^^^ pp_id id
  ^^^ P.parens (comma_list (pp_declaration file) args)
  ^^^ (pp_statement_l file s)
*)



let pp_program (startup, defs) =
  List.fold_left (fun acc ->
    function
      | (id, Left ((return_ty, params, is_variadic), body_opt)) ->
          pp_ctype return_ty ^^^ pp_id id ^^
            P.parens (comma_list (fun (id, (qs, ty)) -> (pp_qualifiers qs (pp_ctype ty)) ^^^ pp_id id) params ^^
              if is_variadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty
            ) ^^
          (match body_opt with
             | Some body -> P.space ^^ pp_statement body
             | None      -> P.semi
          ) ^^ P.break 1 ^^ P.hardline ^^ acc
      | (id, Right (qs, ty, e_opt)) ->
          (pp_qualifiers qs (pp_ctype ty)) ^^^ pp_id id ^^^
          P.optional (fun e -> P.equals ^^^ pp_expression e) e_opt ^^ P.semi ^^ P.break 1 ^^ P.hardline ^^ acc
  ) P.empty defs
