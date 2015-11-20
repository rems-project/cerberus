open Lem_pervasives
open Either

open Global
open AilSyntax
open AilTypes
open GenTypes

open Colour

let isatty = ref false


module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | AilEunary (PostfixIncr, _)
  | AilEunary (PostfixDecr, _) -> Some 1

  | AilEunary (Plus, _)
  | AilEunary (Minus, _)
  | AilEunary (Bnot, _)
  | AilEunary (Indirection, _)
  | AilEunary (Address0, _) -> Some 2
  
  | AilEbinary (_, Arithmetic Mul0, _)
  | AilEbinary (_, Arithmetic Div0, _)
  | AilEbinary (_, Arithmetic Mod, _) -> Some 3
  
  | AilEbinary (_, Arithmetic Add0, _)
  | AilEbinary (_, Arithmetic Sub0, _) -> Some 4
  
  | AilEbinary (_, Arithmetic Shl, _)
  | AilEbinary (_, Arithmetic Shr, _) -> Some 5
  
  | AilEbinary (_, Lt0, _)
  | AilEbinary (_, Gt, _)
  | AilEbinary (_, Le, _)
  | AilEbinary (_, Ge0, _) -> Some 6
  
  | AilEbinary (_, Eq0, _)
  | AilEbinary (_, Ne, _) -> Some 7
  
  | AilEbinary (_, Arithmetic Band, _) -> Some 8
  
  | AilEbinary (_, Arithmetic Bxor, _) -> Some 9
  
  | AilEbinary (_, Arithmetic Bor, _) -> Some 10
  
  | AilEbinary (_, And0, _) -> Some 11
  
  | AilEbinary (_, Or0, _) -> Some 12
  
  | AilEcond _ -> Some 13
  
  | AilEassign _
  | AilEcompoundAssign _ -> Some 14
  
  | AilEbinary (_, Comma, _) -> Some 15
  
  | _ -> None


let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true



let pp_keyword w      = if !isatty then pp_ansi_format [Bold; Cyan] !^ w else !^ w
let pp_type_keyword w = if !isatty then pp_ansi_format [Green] !^ w else !^ w
let pp_const   c = if !isatty then pp_ansi_format [Magenta] !^ c else !^ c
let pp_comment str = if !isatty then pp_ansi_format [Red] !^ str else !^ str


let pp_id id = !^ (Pp_symbol.to_string_pretty id)
let pp_id_obj id = if !isatty then pp_ansi_format [Yellow] !^ (Pp_symbol.to_string_pretty id) else !^ (Pp_symbol.to_string_pretty id)
let pp_id_label id = if !isatty then pp_ansi_format [Magenta] !^ (Pp_symbol.to_string_pretty id) else !^ (Pp_symbol.to_string_pretty id)
let pp_id_type id = if !isatty then pp_ansi_format [Green] !^ (Pp_symbol.to_string_pretty id) else !^ (Pp_symbol.to_string_pretty id)
let pp_id_func id = if !isatty then pp_ansi_format [Bold; Blue] !^ (Pp_symbol.to_string_pretty id) else !^ (Pp_symbol.to_string_pretty id)


(*
let pp_symbol  a = !^ (if !isatty then ansi_format [Blue] (Pp_symbol.to_string_pretty a) else (Pp_symbol.to_string_pretty a))
let pp_number  n = !^ (if !isatty then ansi_format [Yellow] n else n)
let pp_impl    i = P.angles (!^ (if !isatty then ansi_format [Yellow] (Implementation_.string_of_implementation_constant i)
                                            else Implementation_.string_of_implementation_constant i))
*)




let pp_storageDuration = function
  | Static    -> pp_keyword "static"
  | Thread    -> pp_keyword "thread"
  | Automatic -> pp_keyword "automatic"
  | Allocated -> pp_keyword "allocated"


let pp_cond switch str =
  if switch then
    (^^^) (pp_keyword str)
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


let string_of_integerBaseType = function
 | Ichar          -> "char"
 | Short          -> "short"
 | Int_           -> "int"
 | Long           -> "long"
 | LongLong       -> "long long"
 | IntN_t n       -> "int" ^ string_of_int n ^ "_t"
 | Int_leastN_t n -> "int_least" ^ string_of_int n ^ "_t"
 | Int_fastN_t n  -> "int_fast" ^ string_of_int n ^ "_t"
 | Intmax_t       -> "intmax_t"
 | Intptr_t       -> "intptr_t"



let pp_integerType = function
 | Char ->
     pp_type_keyword "char"
 | Bool ->
     pp_type_keyword "_Bool"
 | Signed ((IntN_t _ | Int_leastN_t _ | Int_fastN_t _ | Intmax_t | Intptr_t) as ibty) ->
     pp_type_keyword (string_of_integerBaseType ibty)
 | Unsigned ((IntN_t _ | Int_leastN_t _ | Int_fastN_t _ | Intmax_t | Intptr_t) as ibty) ->
     pp_type_keyword ("u" ^ string_of_integerBaseType ibty)
 | Size_t ->
     pp_type_keyword "size_t"
 | Ptrdiff_t ->
     pp_type_keyword "ptrdiff_t"
 | Signed ibty ->
     pp_type_keyword "signed" ^^^ !^ (string_of_integerBaseType ibty)
 | Unsigned ibty ->
     pp_type_keyword "unsigned" ^^^ !^ (string_of_integerBaseType ibty)
 | IBuiltin str ->
     pp_type_keyword str
 | Enum sym ->
     pp_type_keyword "enum" ^^^ pp_id sym


let pp_realFloatingType = function
  | Float ->
      pp_type_keyword "float"
  | Double ->
      pp_type_keyword "double"
  | LongDouble ->
      pp_type_keyword "long" ^^^ pp_type_keyword "double"


let pp_floatingType = function
  | RealFloating ft ->
      pp_realFloatingType ft

let pp_basicType = function
  | Integer it ->
      pp_integerType it
  | Floating rft ->
      pp_floatingType rft


let pp_integer i = P.string (Nat_big_num.to_string i)



let pp_integerBaseType_raw = function
  | Ichar ->
      !^ "Ichar"
  | Short ->
      !^ "Short"
  | Int_ ->
      !^ "Int_"
  | Long ->
      !^ "Long"
  | LongLong ->
      !^ "LongLong"
  | IntN_t n ->
      !^ "IntN_t" ^^ P.brackets (!^ (string_of_int n))
  | Int_leastN_t n ->
      !^ "Int_leastN_t" ^^ P.brackets (!^ (string_of_int n))
  | Int_fastN_t n ->
      !^ "Int_fastN_t" ^^ P.brackets (!^ (string_of_int n))
  | Intmax_t ->
      !^ "Intmax_t"
  | Intptr_t ->
      !^ "Intptr_t"

(*
  | Int8_t ->
      !^ "Int8_t"
  | Int16_t ->
      !^ "Int16_t"
  | Int32_t ->
      !^ "Int32_t"
  | Int64_t ->
      !^ "Int64_t"
*)

let pp_integerType_raw = function
 | Char ->
     !^ "Char"
 | Bool ->
     !^ "Bool"
 | Signed ibty ->
     !^ "Signed" ^^ P.brackets (pp_integerBaseType_raw ibty)
 | Unsigned ibty ->
     !^ "Unsigned" ^^ P.brackets (pp_integerBaseType_raw ibty)
 | IBuiltin str ->
     !^ str
 | Enum sym ->
     !^ "enum" ^^^ pp_id sym
 | Size_t ->
     !^ "Size_t"
 | Ptrdiff_t ->
     !^ "Ptrdiff_t"



let pp_realFloatingType_raw = function
  | Float ->
      !^ "Float"
  | Double ->
      !^ "Double"
  | LongDouble ->
      !^ "LongDouble"

let pp_floatingType_raw = function
  | RealFloating rfty ->
      !^ "RealFloating" ^^ P.brackets(pp_realFloatingType_raw rfty)

let pp_basicType_raw = function
  | Integer ity ->
      !^ "Integer" ^^ P.brackets (pp_integerType_raw ity)
  | Floating fty ->
      !^ "Floating" ^^ P.brackets (pp_floatingType_raw fty)

let pp_qualifiers_raw qs =
  let f (str, b) =
    !^ str ^^ P.equals ^^^ !^ (if b then "true" else "false") in
  P.braces (comma_list f [("const", qs.const); ("restrict", qs.restrict); ("volatile", qs.volatile); ("atomic", qs.atomic)])

let rec pp_ctype_raw = function
  | Void ->
      !^ "Void"
  | Basic bty ->
      !^ "Basic" ^^ P.brackets (pp_basicType_raw bty)
  | Array (ty, None) ->
      !^ "Array" ^^ P.brackets (pp_ctype_raw ty ^^ P.comma ^^^ !^ "None")
  | Array (ty, Some n) ->
      !^ "Array" ^^ P.brackets (pp_ctype_raw ty ^^ P.comma ^^^ !^ "Some" ^^ P.brackets (pp_integer n))
  | Function (has_proto, ty, params, is_variadic) ->
      !^ "Function" ^^ P.brackets (!^ (if has_proto then "true" else "false") ^^ P.comma ^^^
                                        comma_list (fun (qs, ty) -> P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)) params ^^ P.comma ^^
                                   !^ (if is_variadic then "true" else "false"))
  | Pointer (ref_qs, ref_ty) ->
      !^ "Pointer" ^^ P.brackets (pp_qualifiers_raw ref_qs ^^ P.comma ^^^ pp_ctype_raw ref_ty)
  | Atomic ty ->
      !^ "Atomic" ^^ P.brackets (pp_ctype_raw ty)
  | Struct sym ->
      !^ "Struct" ^^ pp_id sym
(*
      !^ "Struct" ^^ P.brackets (
        pp_id sym ^^ P.comma ^^^
        comma_list (fun (ident, ty) -> P.parens (Pp_cabs.pp_cabs_identifier ident ^^ P.comma ^^^ pp_ctype_raw ty)) xs
      )
*)
  | Union sym ->
      !^ "Union" ^^ pp_id sym
(*
      !^ "Union" ^^ P.brackets (
        pp_id sym ^^ P.comma ^^^
        comma_list (fun (ident, ty) -> P.parens (Pp_cabs.pp_cabs_identifier ident ^^ P.comma ^^^ pp_ctype_raw ty)) xs
      )
*)
  | Builtin str ->
      !^ "Builtin" ^^ P.brackets (!^ str)



let rec pp_ctype = function
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      pp_type_keyword "void"
  | Basic  b ->
      pp_basicType b
  | Array (ty, n_opt) ->
      pp_ctype ty ^^ P.brackets (P.optional pp_integer n_opt)
  | Function (has_proto, ty, ps, is_variadic) ->
      pp_ctype ty ^^ P.parens (
        let p = comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype t)) ps in
        if is_variadic then
          p ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
        else
          p
      )
  | Pointer (ref_qs, ref_ty) ->
      pp_qualifiers ref_qs (pp_ctype ref_ty) ^^ P.star
  | Atomic ty ->
      pp_keyword "_Atomic" ^^ P.parens (pp_ctype ty)
  | Struct sym ->
      pp_keyword "struct" ^^^ pp_id_type sym
  | Union sym ->
      pp_keyword "union" ^^^ pp_id_type sym
(*
  | Struct (tag, ident_tys) ->
      pp_keyword "struct" ^^^ pp_id_type tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
  | Union (tag, ident_tys) ->
      pp_keyword "union" ^^^ pp_id_type tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
*)
  | Builtin str ->
      !^ str


let rec pp_ctype_declaration id = function
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      pp_type_keyword "void" ^^^ id
  | Basic  b ->
      pp_basicType b ^^^ id
  | Array (ty, n_opt) ->
      pp_ctype ty ^^^ id ^^ P.brackets (P.optional pp_integer n_opt)
  | Function (has_proto, ty, ps, is_variadic) ->
      pp_ctype_declaration id ty ^^ P.parens (
        let p = comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype t)) ps in
        if is_variadic then
          p ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
        else
          p
      )
  | Pointer (ref_qs, ref_ty) ->
      pp_qualifiers ref_qs (pp_ctype ref_ty) ^^ P.star
  | Atomic ty ->
      pp_keyword "_Atomic" ^^ P.parens (pp_ctype ty)
  | Struct sym ->
      pp_keyword "struct" ^^^ pp_id_type sym
  | Union sym ->
      pp_keyword "union" ^^^ pp_id_type sym
(*
  | Struct (tag, ident_tys) ->
      pp_keyword "struct" ^^^ pp_id_type tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys) ^^^ id
  | Union (tag, ident_tys) ->
      pp_keyword "union" ^^^ pp_id_type tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys) ^^^ id
*)
  | Builtin str ->
      !^ str


(* pprint C types in human readable format *)
let pp_qualifiers_human qs =
  let strs =
    (if qs.const then fun z -> "const" :: z else (fun z -> z)) (
      (if qs.restrict then fun z -> "restrict" :: z else (fun z -> z)) (
        (if qs.volatile then fun z -> "volatile" :: z else (fun z -> z)) (
          (if qs.atomic then fun z -> "atomic" :: z else (fun z -> z))
            []
        )
      )
    ) in
  P.braces (
    comma_list (!^) strs
  )

let rec pp_ctype_human qs ty =
  let prefix_pp_qs =
    if AilTypesAux.is_unqualified qs then
      P.empty
    else
      pp_qualifiers_human qs ^^ P.space in

  match ty with
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      prefix_pp_qs ^^ !^ "void"
  | Basic  b ->
      prefix_pp_qs ^^ pp_basicType b
  | Array (ty, n_opt) ->
      !^ "array" ^^^ P.optional pp_integer n_opt ^^^ !^ "of" ^^^ pp_ctype_human qs ty
  | Function (has_proto, ret_ty, params, is_variadic) ->
      if not (AilTypesAux.is_unqualified qs) then
        print_endline "TODO: warning, found qualifiers in a function type (this is an UB)";
      
      !^ (if is_variadic then "variadic function" else "function") ^^^
      P.parens (
        comma_list (fun (qs', ty') ->
          pp_ctype_human qs' ty' (* NOTE: qs should be no_qualifiers, here *)
        ) params
      ) ^^^
      !^ "returning" ^^^ pp_ctype_human qs ret_ty
  | Pointer (ref_qs, ref_ty) ->
      pp_qualifiers_human qs ^^^ !^ "pointer to" ^^^ pp_ctype_human ref_qs ref_ty
  | Atomic ty ->
      !^ "atomic" ^^^ pp_ctype_human qs ty
  | Struct sym ->
      !^ "struct" ^^^ pp_id sym
  | Union sym ->
      !^ "union" ^^^ pp_id sym
(*
  | Struct (tag, ident_tys) ->
      !^ "struct" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype_human qs ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
  | Union (tag, ident_tys) ->
      !^ "union" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype_human qs ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
*)
  | Builtin str ->
      prefix_pp_qs ^^ !^ str








let pp_arithmeticOperator = function
  | Mul0  -> P.star
  | Div0  -> P.slash
  | Mod  -> P.percent
  | Add0  -> P.plus
  | Sub0  -> P.minus
  | Shl  -> P.langle ^^ P.langle
  | Shr  -> P.rangle ^^ P.rangle
  | Band -> P.ampersand
  | Bor  -> P.bar
  | Bxor -> P.caret


let pp_binaryOperator = function
  | Arithmetic o -> pp_arithmeticOperator o
  | Comma        -> P.comma
  | And0          -> P.ampersand ^^ P.ampersand
  | Or0           -> P.bar ^^ P.bar
  | Lt0           -> P.langle
  | Gt           -> P.rangle
  | Le           -> P.langle ^^ P.equals
  | Ge0           -> P.rangle ^^ P.equals
  | Eq0           -> P.equals ^^ P.equals
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

(*
let rec string_of_octal_big_int n =
  let (n', r) = Nat_big_int.quomod n in
  match r with
    | 
 *)




(* TODO: should reverse the decoding of n *)
let pp_integerConstant = function
  | IConstant (n, basis, suff_opt) ->
      !^ (match basis with
            | Octal       -> String_nat_big_num.string_of_octal n
            | Decimal     -> String_nat_big_num.string_of_decimal n
            | Hexadecimal -> String_nat_big_num.string_of_hexadecimal n
         )  ^^ (P.optional pp_integerSuffix suff_opt)
  | IConstantMax ity ->
      !^ "TODO[IConstantMax]"
  | IConstantMin ity ->
      !^ "TODO[IConstantMin]"


let pp_floatingConstant str =
  !^ str

let pp_characterPrefix pref =
  let to_string = function
    | Pref_L -> "L"
    | Pref_u -> "u"
    | Pref_U -> "U"
  in
  P.string (to_string pref)

let pp_characterConstant (pref_opt, c) =
  (P.optional pp_characterPrefix pref_opt) ^^ P.squotes (!^ c)


let pp_encodingPrefix pref =
  let to_string = function
    | Enc_u8 -> "u8"
    | Enc_u  -> "u"
    | Enc_U  -> "U"
    | Enc_L  -> "L"
  in
  P.string (to_string pref)

let pp_stringLiteral (pref_opt, strs) =
  (P.optional pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Green] (P.dquotes (!^ (String.concat "" strs)))


let rec pp_constant = function
  | ConstantIndeterminate ty ->
      pp_keyword "indet" ^^ P.parens (pp_ctype_raw ty)
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
     !^ "TODO[ConstantStruct]"
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






let rec pp_expression_aux mk_pp_annot a_expr =
  let rec pp p (AnnotatedExpression (annot, loc, expr)) =
    let p' = precedence expr in
    let pp z = P.group (pp p' z) in
    (if lt_precedence p' p then fun z -> z else P.parens)
      (mk_pp_annot annot (match expr with
(*
        | STRING_LITERAL lit ->
            pp_string_literal lit
*)
        | AilEunary (PostfixIncr as o, e)
        | AilEunary (PostfixDecr as o, e) ->
            pp e ^^ pp_unaryOperator o
        | AilEunary (o, e) ->
            pp_unaryOperator o ^^ pp e
        | AilEbinary (e1, (Comma as o), e2) ->
            pp e1 ^^ pp_binaryOperator o ^^ P.space ^^ pp e2
        | AilEbinary (e1, o, e2) ->
            pp e1 ^^^ pp_binaryOperator o ^^^ pp e2
        | AilEassign (e1, e2) ->
            pp e1 ^^^ P.equals ^^^ pp e2
        | AilEcompoundAssign (e1, o, e2) ->
            pp e1 ^^^ pp_arithmeticOperator o ^^ P.equals ^^^ pp e2
        | AilEcond (e1, e2, e3) ->
            P.group (pp e1 ^^^ P.qmark ^^^ pp e2 ^^^ P.colon ^^^ pp e3)
        | AilEcast (qs, ty, e) ->
            (* TODO *)
            P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty) ^^^ pp e
(*
            pp_qualifiers qs (P.parens (pp_ctype ty)) ^^^ pp e
*)
        | AilEcall (e, es) ->
            pp e ^^ P.parens (comma_list pp es)
        | AilEassert e ->
            !^ "assert" ^^ P.parens (pp e)
        | AilEoffsetof (ty, ident) ->
            !^ "offsetof" ^^ P.parens (pp_ctype_raw ty ^^ P.comma ^^^ Pp_cabs.pp_cabs_identifier ident)
        | AilEgeneric (e, gas) ->
            pp_keyword "_Generic" ^^ P.parens (pp e ^^ P.comma ^^^ comma_list (pp_generic_association_aux mk_pp_annot) gas)
        | AilEarray (ty, e_opts) ->
            P.braces (comma_list (function Some e -> pp e | None -> !^ "_") e_opts)
        | AilEstruct (tag_sym, xs) ->
            P.braces (comma_list (function (ident, Some e) -> pp e | (ident, None) -> !^ "_") xs)
        | AilEcompound (ty, e) ->
            P.parens (pp_ctype ty) ^^ P.braces (pp e)
        | AilEbuiltin str ->
            !^ str
        | AilEstr lit ->
            pp_stringLiteral lit
        | AilEconst c ->
            pp_constant c
        | AilEident x ->
            pp_id x
        | AilEsizeof (qs, ty) ->
            (* TODO *)
            pp_keyword "sizeof" ^^ P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)
(*            pp_keyword "sizeof" ^^ P.parens (pp_qualifiers qs (pp_ctype ty)) *)
        | AilEsizeof_expr e ->
            pp_keyword "sizeof" ^^^ pp e
        | AilEalignof (qs, ty) ->
            (* TODO *)
            pp_keyword "Alignof_" ^^ P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)
(*            pp_keyword "Alignof_" ^^ P.parens (pp_qualifiers qs (pp_ctype ty)) *)

        | AilEmemberof (e, ident) ->
            pp e ^^ P.dot ^^ Pp_cabs.pp_cabs_identifier ident
        | AilEmemberofptr (e, ident) ->
            pp e ^^ (!^ "->") ^^ Pp_cabs.pp_cabs_identifier ident

        | AilEannot (_, e) ->
            !^ "/* annot */" ^^^ pp e
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
        | AilEva_start (e, sym) ->
            pp_keyword "va_start" ^^ P.parens (pp e ^^ P.comma ^^^ pp_id sym)
        | AilEva_arg (e, ty) ->
            pp_keyword "va_arg" ^^ P.parens (pp e ^^ P.comma ^^^ pp_ctype_raw ty)
      )) in
  pp None a_expr

and pp_generic_association_aux pp_annot = function
  | AilGAtype (ty, e) ->
      pp_ctype_raw ty ^^ P.colon ^^^ pp_expression_aux pp_annot e
  | AilGAdefault e ->
      pp_keyword "default" ^^ P.colon ^^^ pp_expression_aux pp_annot e



(*
let pp_definition file (name, e) = 
  let (ty, _) = Pmap.find name file.id_map in
  pp_ctype_raw ty ^^^ pp_id name ^^^ P.equals ^^^ pp_expression_t e
*)

(*
let pp_typed_id file name =
  let (q, t, _) = Pmap.find name file.id_map in
  pp_id name ^^ P.colon ^^^ (pp_qualifiers q $ pp_ctype t)
*)

let rec pp_statement_aux pp_annot (AnnotatedStatement (_, stmt)) =
  let pp_statement = pp_statement_aux pp_annot in
(*
  let nest' (_, stmt) =
    match stmt with
      | BLOCK _ -> 
*)
  match stmt with
    | AilSskip ->
        P.semi
    | AilSexpr e ->
        pp_expression_aux pp_annot e ^^ P.semi
    | AilSblock ([], ss) ->
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ (P.separate_map (P.break 1) pp_statement ss)) ^/^ P.rbrace
    | AilSblock (ids, ss) ->
        let block =
          P.separate_map
            (P.semi ^^ P.break 1)
            (fun (id, (dur_opt, qs, ty)) -> (* TODO: pp_qualifiers qs (pp_ctype ty) *) P.parens (P.optional pp_storageDuration dur_opt ^^^ pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty) ^^^ pp_id_obj id)
            ids ^^ P.semi ^^ P.break 1 ^^
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
        P.empty
    (* TODO: looks odd *)
    | AilSdeclaration defs ->
        comma_list (fun (id, e) -> pp_id_obj id ^^^ P.equals ^^^ pp_expression_aux pp_annot e) defs ^^
        P.semi ^^^ pp_comment "// decl"
    | AilSpar ss ->
        P.lbrace ^^ P.lbrace ^^ P.lbrace ^^ P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1 ^^ !^ "|||" ^^ P.break 1) pp_statement ss) ^/^ P.rbrace ^^ P.rbrace ^^ P.rbrace



(*
let pp_sigma_declaration = function
  | SDecl_fun (id, fdecl) ->
      !^ "define" ^^^ pp_id id ^^^ !^ "as" ^^^
      (if fdecl.fun_is_variadic then !^ "variadic function" else !^ "function") ^^^
      P.parens (comma_list (fun (id, (qs, ty)) -> (pp_qualifiers qs (pp_ctype ty)) ^^^ pp_id id) fdecl.fun_bindings) ^^^
      !^ "returning" ^^^ pp_ctype fdecl.fun_return_ty ^^^ !^ "with body:" ^^^ P.hardline ^^
      P.optional pp_statement fdecl.fun_body

  | SDecl_global (id, (qs, ty, _)) ->
      !^ "declare" ^^^ pp_id id ^^^ !^ "as" ^^^
      pp_qualifiers qs (pp_ctype ty)
  | SDecl_static_assert (e, strCst) ->
      !^ "SDecl_static_assert"
*)





let pp_static_assertion pp_annot (e, lit) =
  pp_keyword "_Static_assert" ^^ P.parens (pp_expression_aux pp_annot e ^^ P.comma ^^^ pp_stringLiteral lit)


let pp_tag_definition (tag, def) =
  match def with
    | StructDef ident_tys ->
        pp_keyword "struct" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys
          ) ^^ P.break 1
        ) ^^ P.semi
    | UnionDef ident_tys ->
        pp_keyword "union" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys
          ) ^^ P.break 1
        ) ^^ P.semi

let pp_program pp_annot (startup, sigm) =
  isatty := Unix.isatty Unix.stdout;
  P.separate_map (P.break 1 ^^ P.break 1) (pp_static_assertion pp_annot) sigm.static_assertions ^^ P.break 1 ^^ P.break 1 ^^ P.break 1 ^^
  
  (* Tag declarations *)
  P.separate_map (P.break 1 ^^ P.break 1) pp_tag_definition sigm.tag_definitions ^^ P.break 1 ^^ P.break 1 ^^ P.break 1 ^^
  
  List.fold_left (fun acc (sym, decl) ->
    match decl with
      | Decl_object (sd, qs, ty) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          (if !isatty then !^ "\x1b[31m" else P.empty) ^^
(*          !^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ (pp_qualifiers qs (pp_ctype_human ty)) ^^ *)
          !^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ (pp_ctype_human qs ty) ^^
          (if !isatty then !^ "\x1b[0m" else P.empty) ^^ P.hardline ^^
          
(* TODO:
          (pp_qualifiers qs (pp_ctype_declaration (pp_id_obj sym) ty)) ^^^
*)
          pp_id_obj sym ^^ P.colon ^^^ P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty) ^^^

          P.optional (fun e ->
            P.equals ^^^ pp_expression_aux pp_annot e
          ) (Context.lookup identifierEqual sigm.object_definitions sym) ^^ P.semi ^^
          P.break 1 ^^ P.hardline ^^ acc
      
      | Decl_function (has_proto, return_ty, params, is_variadic, is_inline, is_Noreturn) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          (if !isatty then !^ "\x1b[31m" else P.empty) ^^
          !^ "// declare" ^^^ pp_id sym ^^^
          (if has_proto then !^ "WITH PROTO " else P.empty) ^^
          !^ "as" ^^^ pp_ctype_human no_qualifiers (Function (has_proto, return_ty, params, is_variadic)) ^^
          (if !isatty then !^ "\x1b[0m" else P.empty) ^^ P.hardline ^^
          
          (fun k -> if is_inline   then !^ "inline"    ^^^ k else k) (
            (fun k -> if is_Noreturn then !^ "_Noreturn" ^^^ k else k) (
(* TODO:              pp_ctype_declaration (pp_id_func sym) return_ty ^^ *)
              pp_ctype_raw return_ty ^^^ pp_id_func sym ^^
              (match Context.lookup identifierEqual sigm.function_definitions sym with
                | Some (param_syms, stmt) ->
                    P.parens (
                      comma_list (fun (sym, (qs, ty)) ->
                        pp_id_obj sym ^^ P.colon ^^^ P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)
                        
(* TODO:                        (pp_qualifiers qs (pp_ctype ty)) ^^^ pp_id_obj sym *)
                      ) (List.combine param_syms params) ^^
                      if is_variadic then
                        P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                      else
                        P.empty
                    ) ^^^
                    pp_statement_aux pp_annot stmt
                | None ->
                    P.parens (
                      comma_list (fun (qs, ty) ->
                        P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)
(* TODO:                        pp_qualifiers qs (pp_ctype ty) *)
                      ) params ^^
                      if is_variadic then
                        P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                      else
                        P.empty
                    ) ^^ P.semi
              )
            )
          )  ^^
          P.break 1 ^^ P.hardline ^^ acc
    ) P.empty (List.rev sigm.declarations) ^^ P.break 1




let rec pp_genIntegerType = function
 | Concrete ity ->
     !^ "Concrete" ^^ P.brackets (pp_integerType_raw ity)
 | SizeT ->
     !^ "SizeT"
 | PtrdiffT ->
     !^ "PtrdiffT"
 | Unknown iCst ->
     !^ "Unknown" ^^ P.brackets (pp_integerConstant iCst)
 | Promote gity ->
     !^ "Promote" ^^ P.brackets (pp_genIntegerType gity)
 | Usual (gity1, gity2) ->
     !^ "Usual" ^^ P.brackets (pp_genIntegerType gity1 ^^ P.comma ^^^ pp_genIntegerType gity2)



let pp_genBasicType = function
 | GenInteger gity ->
     pp_genIntegerType gity
 | GenFloating fty ->
     pp_floatingType fty

let pp_genType = function
 | GenVoid ->
     !^ "GenVoid"
 | GenBasic gbty ->
     pp_genBasicType gbty
  | GenArray (ty, None) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_raw ty ^^ P.comma ^^^ !^ "None")
  | GenArray (ty, Some n) ->
      !^ "GenArray" ^^ P.brackets (pp_ctype_raw ty ^^ P.comma ^^^ !^ "Some" ^^ P.brackets (pp_integer n))

     
 | GenFunction (has_proto, ty, params, is_variadic) ->
      !^ "GenFunction" ^^ P.brackets (comma_list (fun (qs, ty) -> P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty)) params ^^ P.comma ^^
                                   !^ (if is_variadic then "true" else "false"))

 | GenPointer (ref_qs, ref_ty) ->
      !^ "GenPointer" ^^ P.brackets (pp_qualifiers_raw ref_qs ^^ P.comma ^^^ pp_ctype_raw ref_ty)
  | GenStruct sym ->
      !^ "GenStruct" ^^ pp_id sym
  | GenUnion sym ->
      !^ "GenUnion" ^^ pp_id sym
  | GenAtomic ty ->
      !^ "GenAtomic" ^^ pp_ctype_raw ty
  | GenBuiltin str ->
      !^ "GenBuiltin" ^^ P.brackets (!^ str)


let pp_genTypeCategory = function
 | GenLValueType (qs, ty) ->
     !^ "GenLValueType" ^^ P.brackets (pp_qualifiers qs P.comma ^^^ pp_ctype_raw ty)
 | GenRValueType gty ->
     !^ "GenRValueType" ^^ P.brackets (pp_genType gty)





let pp_expression e = pp_expression_aux (fun _ d -> d) e
let pp_generic_association ga = pp_generic_association_aux (fun _ d -> d) ga
let pp_statement s = pp_statement_aux (fun _ d -> d) s
let pp_program_with_annot prog = pp_program (fun annot z -> P.braces (pp_genTypeCategory annot) ^^ P.brackets z) prog
