open Lem_pervasives
open Either

open AilSyntax
open Ctype
open GenTypes

open Colour

open Pp_ail_raw

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | AilEreg_load _
  | AilEunary (PostfixIncr, _)
  | AilEunary (PostfixDecr, _)
  | AilEcall _
  | AilEmemberof _
  | AilEmemberofptr _ -> Some 1

  | AilEunary (Plus, _)
  | AilEunary (Minus, _)
  | AilEunary (Bnot, _)
  | AilEunary (Indirection, _)
  | AilEunary (Address, _) -> Some 2
  
  | AilEbinary (_, Arithmetic Mul, _)
  | AilEbinary (_, Arithmetic Div, _)
  | AilEbinary (_, Arithmetic Mod, _) -> Some 3
  
  | AilEbinary (_, Arithmetic Add, _)
  | AilEbinary (_, Arithmetic Sub, _) -> Some 4
  
  | AilEbinary (_, Arithmetic Shl, _)
  | AilEbinary (_, Arithmetic Shr, _) -> Some 5
  
  | AilEbinary (_, Lt, _)
  | AilEbinary (_, Gt, _)
  | AilEbinary (_, Le, _)
  | AilEbinary (_, Ge, _) -> Some 6
  
  | AilEbinary (_, Eq, _)
  | AilEbinary (_, Ne, _) -> Some 7
  
  | AilEbinary (_, Arithmetic Band, _) -> Some 8
  
  | AilEbinary (_, Arithmetic Bxor, _) -> Some 9
  
  | AilEbinary (_, Arithmetic Bor, _) -> Some 10
  
  | AilEbinary (_, And, _) -> Some 11
  
  | AilEbinary (_, Or, _) -> Some 12
  
  | AilEcond _ -> Some 13
  
  | AilEassign _
  | AilEcompoundAssign _ -> Some 14
  
  | AilEbinary (_, Comma, _) -> Some 15
  
  | _ -> None


let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true



let pp_keyword w      = !^ (ansi_format [Bold; Cyan] w)
let pp_type_keyword w = !^ (ansi_format [Green] w)
let pp_const c        = !^ (ansi_format [Magenta] c)
let pp_comment str    = !^ (ansi_format [Red] str)


let pp_id id = !^ (Pp_symbol.to_string_pretty id)
let pp_id_obj id = !^ (ansi_format [Yellow] (Pp_symbol.to_string_pretty id))
let pp_id_label id = !^ (ansi_format [Magenta] (Pp_symbol.to_string_pretty id))
let pp_id_type id = !^ (ansi_format [Green] (Pp_symbol.to_string_pretty id))
let pp_id_func id = !^ (ansi_format [Bold; Cyan] (Pp_symbol.to_string_pretty id))


let pp_integer i = P.string (Nat_big_num.to_string i)


(* -- TYPES -- *)
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

let pp_qualifiers qs =
  pp_cond qs.const "const" (
    pp_cond qs.restrict "restrict" (
      pp_cond qs.volatile "volatile" P.empty
    )
  )

(* pprint C types in human readable format *)
let pp_qualifiers_human qs =
  let strs =
    (if qs.const then fun z -> "const" :: z else (fun z -> z)) (
      (if qs.restrict then fun z -> "restrict" :: z else (fun z -> z)) (
        (if qs.volatile then fun z -> "volatile" :: z else (fun z -> z)) (
(*          (if qs.atomic then fun z -> "atomic" :: z else (fun z -> z)) *)
            []
        )
      )
    ) in
  P.braces (
    comma_list (!^) strs
  )


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

let macro_string_of_integerBaseType = function
 | Ichar          -> "CHAR"
 | Short          -> "SHRT"
 | Int_           -> "INT"
 | Long           -> "LONG"
 | LongLong       -> "LLONG"
 | IntN_t n       -> "INT" ^ string_of_int n
 | Int_leastN_t n -> "INT_LEAST" ^ string_of_int n
 | Int_fastN_t n  -> "INT_FAST" ^ string_of_int n
 | Intmax_t       -> "INTMAX"
 | Intptr_t       -> "INTPTR"


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
 | Wchar_t ->
     pp_type_keyword "wchar_t"
 | Wint_t ->
     pp_type_keyword "wint_t"
 | Ptrdiff_t ->
     pp_type_keyword "ptrdiff_t"
 | Vaddr_t ->
     pp_type_keyword "vaddr_t"
 | Signed ibty ->
     pp_type_keyword "signed" ^^^ !^ (string_of_integerBaseType ibty)
 | Unsigned ibty ->
     pp_type_keyword "unsigned" ^^^ !^ (string_of_integerBaseType ibty)
 | Enum sym ->
     pp_type_keyword "enum" ^^^ pp_id sym

let macro_string_of_integerType = function
 | Char ->
     "CHAR"
 | Bool ->
     (* NOTE: this doesn't exists in STD, since the min/max values are know *)
     "BOOL"
 | Signed ibty ->
     (macro_string_of_integerBaseType ibty)
 | Unsigned ibty ->
     "U" ^ macro_string_of_integerBaseType ibty
 | Size_t ->
     "SIZE"
 | Wchar_t ->
     "WCHAR"
 | Wint_t ->
     "WINT"
 | Ptrdiff_t ->
     "PTRDIFF"
 | Vaddr_t ->
     "VADDR"
 | Enum sym ->
     (* NOTE: this is hackish, these don't exists in C11 *)
     "ENUM_" ^ Pp_symbol.to_string_pretty sym


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

let pp_ctype_aux pp_ident_opt qs (Ctype (_, ty) as cty) =
  let precOf = function
    | Void
    | Basic _
    | Atomic _
    | Struct _
    | Union _ ->
        0
    | Array _ ->
        1
    | Function _
    | FunctionNoParams _ ->
        2
    | Pointer _ ->
        3
  in
  let rec aux p qs (Ctype (_, ty)) : P.document -> P.document =
    let p' = precOf ty in
    let aux = aux p' in
    let wrap z = if p' > 0 && p' > p then z else P.parens z in
    begin match ty with
      | Void ->
          fun k -> pp_qualifiers qs ^^ pp_type_keyword "void" ^^ k
      | Basic bty ->
          fun k -> pp_qualifiers qs ^^ pp_basicType bty ^^ k
      | Array (elem_ty, n_opt) ->
          fun k -> aux qs elem_ty k ^^ P.brackets (P.optional pp_integer n_opt)
      | Function ((ret_qs, ret_ty), params, isVariadic) ->
          fun k -> aux ret_qs ret_ty P.empty ^^^
                   P.parens (
                     (if List.length params = 0 then !^"void" else comma_list (fun (qs, ty, _) -> aux qs ty P.empty) params) ^^
                     (if isVariadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
                   ) ^^ k
      | FunctionNoParams ((ret_qs, ret_ty)) ->
          fun k -> aux ret_qs ret_ty P.empty ^^^ P.parens (P.empty) ^^ k
      | Pointer (ref_qs, ref_ty) ->
          fun k ->
            begin match ref_ty with
              | Ctype (_, Function ((ret_qs, ret_ty), params, isVariadic)) ->
                aux ret_qs ret_ty P.empty ^^^ P.parens (!^"*") ^^^
                P.parens (
                  (if List.length params = 0 then !^"void" else comma_list (fun (qs, ty, _) -> aux qs ty P.empty) params) ^^
                  (if isVariadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
                ) ^^ k
              | _ -> aux ref_qs ref_ty (wrap (P.star ^^ pp_qualifiers qs ^^ k))
            end
      | Atomic ty ->
          fun k ->
            pp_qualifiers qs ^^ pp_keyword "_Atomic" ^^
(*        P.parens (pp_ctype_aux None no_qualifiers ty) ^^ pp_spaced_ident *)
            P.parens (aux no_qualifiers ty P.empty) ^^ k
      | Struct sym ->
          fun k ->
            pp_qualifiers qs ^^ pp_keyword "struct" ^^^ pp_id_type sym ^^ k
      | Union sym ->
          fun k ->
            pp_qualifiers qs ^^ pp_keyword "union" ^^^ pp_id_type sym ^^ k
    end in
  (*let pp_ident =
    match pp_ident_opt with Some pp_ident -> pp_ident | None -> P.empty in*)
  let pp_spaced_ident =
    match pp_ident_opt with Some pp_ident -> P.space ^^ pp_ident | None -> P.empty in
  (aux 1 qs cty) pp_spaced_ident
(*
let rec pp_ctype_aux pp_ident_opt qs ty =
  let pp_ident =
    match pp_ident_opt with Some pp_ident -> pp_ident | None -> P.empty in
  let pp_spaced_ident =
    match pp_ident_opt with Some pp_ident -> P.space ^^ pp_ident | None -> P.empty in
  match ty with
    | Void ->
        pp_qualifiers qs ^^ pp_type_keyword "void" ^^ pp_spaced_ident
    | Basic bty ->
        pp_qualifiers qs ^^ pp_basicType bty ^^ pp_spaced_ident
    | Array (elem_ty, n_opt) ->
        pp_ctype_aux None qs elem_ty ^^ pp_spaced_ident ^^ P.brackets (P.optional pp_integer n_opt)
    | Function (has_proto, (ret_qs, ret_ty), params, isVariadic) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        pp_ctype_aux (
          Some (
            pp_spaced_ident ^^ P.parens (
            let params_doc = comma_list (fun (qs, ty, isRegister) ->
              (fun z -> if isRegister then pp_keyword "register" ^^^ z else z)
                (pp_ctype_aux None qs ty)
            ) params in
            if isVariadic then
              params_doc ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
            else
              params_doc
            )
          )
        ) ret_qs ret_ty
        
(*
        ^^ P.hardline ^^ P.hardline ^^
        
        pp_ctype_aux None ret_qs ret_ty ^^ pp_spaced_ident ^^ P.parens (
          let params_doc = comma_list (fun (qs, ty, isRegister) ->
            (fun z -> if isRegister then pp_keyword "register" ^^^ z else z)
              (pp_ctype_aux None qs ty)
          ) params in
          if isVariadic then
            params_doc ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
          else
            params_doc
        )
*)

    | Pointer (ref_qs, ref_ty) ->
        pp_ctype_aux None ref_qs ref_ty ^^^ P.star ^^^ pp_qualifiers qs ^^ pp_ident
    | Atomic ty ->
        pp_qualifiers qs ^^ pp_keyword "_Atomic" ^^
        P.parens (pp_ctype_aux None no_qualifiers ty) ^^ pp_spaced_ident
    | Struct sym ->
        pp_qualifiers qs ^^ pp_keyword "struct" ^^^ pp_id_type sym ^^ pp_spaced_ident
    | Union sym ->
        pp_qualifiers qs ^^ pp_keyword "union" ^^^ pp_id_type sym ^^ pp_spaced_ident
*)

let pp_ctype qs ty =
  pp_ctype_aux None qs ty

let pp_ctype_declaration pp_ident qs ty =
  pp_ctype_aux (Some pp_ident) qs ty


let rec pp_ctype_human qs (Ctype (_, ty)) =
  let prefix_pp_qs =
    if AilTypesAux.is_unqualified qs then
      P.empty
    else
      pp_qualifiers_human qs ^^ P.space in
  match ty with
    | Void ->
        prefix_pp_qs ^^ !^ "void"
    | Basic bty ->
        prefix_pp_qs ^^ pp_basicType bty
    | Array (elem_ty, n_opt) ->
        (* NOTE: here [qs] is that of the element type *)
        !^ "array" ^^^ P.optional pp_integer n_opt ^^^ !^ "of" ^^^ pp_ctype_human qs elem_ty
    | Function ((ret_qs, ret_ty), params, is_variadic) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        if not (AilTypesAux.is_unqualified qs) then
          print_endline "TODO: warning, found qualifiers in a function type (this is an UB)"; (* TODO: is it really UB? *)
        
        !^ (if is_variadic then "variadic function" else "function") ^^^
        P.parens (
          comma_list (fun (param_qs, param_ty, isRegister) ->
            (fun z -> if isRegister then !^ "register" ^^^ z else z)
              (pp_ctype_human param_qs param_ty)
          ) params
        ) ^^^
        !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
    | FunctionNoParams ((ret_qs, ret_ty)) ->
        (* TODO: warn if [qs] is not empty, this is an invariant violation *)
        if not (AilTypesAux.is_unqualified qs) then
          print_endline "TODO: warning, found qualifiers in a function type (this is an UB)"; (* TODO: is it really UB? *)
        !^ "function (NOPARAMS)" ^^^
        !^ "returning" ^^^ pp_ctype_human ret_qs ret_ty
    | Pointer (ref_qs, ref_ty) ->
        prefix_pp_qs ^^ !^ "pointer to" ^^^ pp_ctype_human ref_qs ref_ty
    | Atomic ty ->
        prefix_pp_qs ^^ !^ "atomic" ^^^ pp_ctype_human no_qualifiers ty
    | Struct tag_sym ->
        prefix_pp_qs ^^ !^ "struct" ^^^ pp_id tag_sym
    | Union tag_sym ->
        prefix_pp_qs ^^ !^ "union" ^^^ pp_id tag_sym

(* -- EXPRESSIONS -- *)
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
  | Bxor -> P.caret


let pp_binaryOperator = function
  | Arithmetic aop -> pp_arithmeticOperator aop
  | Comma          -> P.comma
  | And            -> P.ampersand ^^ P.ampersand
  | Or             -> P.bar ^^ P.bar
  | Lt             -> P.langle
  | Gt             -> P.rangle
  | Le             -> P.langle ^^ P.equals
  | Ge             -> P.rangle ^^ P.equals
  | Eq             -> P.equals ^^ P.equals
  | Ne             -> P.bang   ^^ P.equals


let pp_unaryOperator = function
  | Plus        -> P.plus
  | Minus       -> P.minus
  | Bnot        -> P.tilde
  | Address     -> P.ampersand
  | Indirection -> P.star
  | PostfixIncr -> P.plus ^^ P.plus
  | PostfixDecr -> P.minus ^^ P.minus


let pp_integerSuffix =
  let to_string = function
    | U   -> "U"
    | UL  -> "UL"
    | ULL -> "ULL"
    | L   -> "L"
    | LL  -> "LL" in
  fun z -> P.string (to_string z)


(* TODO: should reverse the decoding of n *)
let pp_integerConstant = function
  | IConstant (n, basis, suff_opt) ->
      !^ (match basis with
            | Octal       -> String_nat_big_num.string_of_octal n
            | Decimal     -> String_nat_big_num.string_of_decimal n
            | Hexadecimal -> String_nat_big_num.string_of_hexadecimal n
         )  ^^ (P.optional pp_integerSuffix suff_opt)
  | IConstantMax ity ->
      pp_const (macro_string_of_integerType ity ^ "_MAX")
  | IConstantMin ity ->
      pp_const (macro_string_of_integerType ity ^ "_MIN")


let pp_floatingConstant (str, suff_opt) =
  !^ str ^^
  begin match suff_opt with
    | None -> P.empty
    | Some Fsuf_F -> !^ "f"
    | Some Fsuf_L -> !^ "l"
  end

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
  let strs = List.concat (List.map snd strs) in
  (P.optional pp_encodingPrefix pref_opt) ^^ pp_ansi_format [Green] (P.dquotes (!^ (String.concat "" strs)))


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
 | ConstantArray (elem_ty, csts) ->
     P.braces (comma_list pp_constant csts)
 | ConstantStruct (tag_sym, xs) ->
     P.parens (!^ "struct" ^^^ pp_id tag_sym) ^^ P.braces (
       comma_list (fun (memb_ident, cst) ->
         P.dot ^^ Pp_symbol.pp_identifier memb_ident ^^ P.equals ^^^ pp_constant cst
       ) xs
     )
 | ConstantUnion (tag_sym, memb_ident, cst) ->
     P.parens (!^ "union" ^^^ pp_id tag_sym) ^^ P.braces (P.dot ^^ Pp_symbol.pp_identifier memb_ident ^^ P.equals ^^^ pp_constant cst)
 
let pp_ail_builtin = function
  | AilBatomic b ->
    begin match b with
      | AilBAthread_fence -> !^"atomic_thread_fence"
      | AilBAstore -> !^"atomic_store_explicit"
      | AilBAload -> !^"atomic_load_explicit"
      | AilBAexchange -> !^"atomic_exchange_explicit"
      | AilBAcompare_exchange_strong -> !^"atomic_compare_exchange_strong_explicit"
      | AilBAcompare_exchange_weak -> !^"atomic_compare_exchange_weak_explicit"
      | AilBAfetch_key -> !^"atomic_fetch_key_explicit"
    end
  | AilBlinux b ->
    begin match b with
      | AilBLfence -> !^"linux_fence"
      | AilBLread -> !^"linux_read"
      | AilBLwrite -> !^"linux_write"
      | AilBLrmw -> !^"linux_rmw"
    end
  | AilBcopy_alloc_id ->
      !^"copy_alloc_id"
  | AilBCHERI str ->
      !^ str

let rec pp_expression_aux mk_pp_annot a_expr =
  let rec pp p (AnnotatedExpression (annot, _, loc, expr)) =
    let p' = precedence expr in
    let pp z = P.group (pp p' z) in
    (if lt_precedence p' p then fun z -> z else P.parens)
      (mk_pp_annot annot (match expr with
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
        | AilEreg_load r ->
            !^("r" ^ string_of_int r)
        | AilEbmc_assume e ->
            !^ "__bmc_assume" ^^ P.parens (pp e)
        | AilEcompoundAssign (e1, o, e2) ->
            pp e1 ^^^ pp_arithmeticOperator o ^^ P.equals ^^^ pp e2
        | AilEcond (e1, e2, e3) ->
            P.group (pp e1 ^^^ P.qmark ^^^ pp e2 ^^^ P.colon ^^^ pp e3)
        | AilEcast (qs, ty, e) ->
            if !Debug_ocaml.debug_level > 5 then
              (* printing the types in a human readable format *)
              P.parens (pp_ctype_human qs ty) ^^^ pp e
            else
              P.parens (pp_ctype qs ty) ^^^ pp e
        | AilEcall (e, es) ->
            pp e ^^ P.parens (comma_list pp es)
        | AilEassert e ->
            !^ "assert" ^^ P.parens (pp e)
        | AilEoffsetof (ty, ident) ->
            !^ "offsetof" ^^ P.parens (pp_ctype no_qualifiers ty ^^ P.comma ^^^ Pp_symbol.pp_identifier ident)
        | AilEgeneric (e, gas) ->
            pp_keyword "_Generic" ^^ P.parens (pp e ^^ P.comma ^^^ comma_list (pp_generic_association_aux mk_pp_annot) gas)
        | AilEarray (_, ty, e_opts) ->
            P.braces (comma_list (function Some e -> pp e | None -> !^ "_") e_opts)
        | AilEstruct (tag_sym, xs) ->
            P.parens (!^ "struct" ^^^ pp_id tag_sym) ^^ P.braces (comma_list (function (ident, Some e) -> pp e | (ident, None) -> !^ "_") xs)
        | AilEunion (tag_sym, memb_ident, e_opt) ->
            P.parens (!^ "union" ^^^ pp_id tag_sym) ^^ P.braces (
              P.dot ^^ Pp_symbol.pp_identifier memb_ident ^^ P.equals ^^^ (function None -> !^ "_" | Some e -> pp e) e_opt
            )
        | AilEcompound (qs, ty, e) ->
            P.parens (pp_ctype qs ty) ^^ P.braces (pp e)
        | AilEbuiltin b ->
            pp_ail_builtin b
        | AilEstr lit ->
            pp_stringLiteral lit
        | AilEconst c ->
            pp_constant c
        | AilEident x ->
            pp_id x
        | AilEsizeof (qs, ty) ->
            if !Debug_ocaml.debug_level > 5 then
              (* printing the types in a human readable format *)
              pp_keyword "sizeof" ^^ P.parens (pp_ctype_human qs ty)
            else
              pp_keyword "sizeof" ^^ P.parens (pp_ctype qs ty)
        | AilEsizeof_expr e ->
            pp_keyword "sizeof" ^^^ pp e
        | AilEalignof (qs, ty) ->
            if !Debug_ocaml.debug_level > 5 then
              (* printing the types in a human readable format *)
              pp_keyword "Alignof_" ^^ P.parens (pp_ctype_human qs ty)
            else
              pp_keyword "Alignof_" ^^ P.parens (pp_ctype qs ty)
        | AilEmemberof (e, ident) ->
            pp e ^^ P.dot ^^ Pp_symbol.pp_identifier ident
        | AilEmemberofptr (e, ident) ->
            pp e ^^ (!^ "->") ^^ Pp_symbol.pp_identifier ident
        | AilEannot (_, e) ->
            !^ "/* annot */" ^^^ pp e
        | AilEva_start (e, sym) ->
            pp_keyword "va_start" ^^ P.parens (pp e ^^ P.comma ^^^ pp_id sym)
        | AilEva_copy (e1, e2) ->
            pp_keyword "va_copy" ^^ P.parens (pp e1 ^^ P.comma ^^^ pp e2)
        | AilEva_arg (e, ty) ->
            pp_keyword "va_arg" ^^ P.parens (pp e ^^ P.comma ^^^ pp_ctype no_qualifiers ty)
        | AilEva_end e ->
            pp_keyword "va_end" ^^ P.parens (pp e)
        | AilErvalue e ->
            pp_keyword "rvalue" ^^ P.parens (pp e)
        | AilEarray_decay e ->
            pp_keyword "array_decay" ^^ P.parens (pp e)
        | AilEfunction_decay e ->
            pp_keyword "function_decay" ^^ P.parens (pp e)
        
        | AilEprint_type e ->
(*            if !Debug_ocaml.debug_level > 5 then
*)
              pp_keyword "__cerb_printtype" ^^ P.parens (pp e)
(*
            else
              pp e
*)
        | AilEgcc_statement ->
            pp_keyword "gcc_statement" (* TODO *)
      )) in
  pp None a_expr

and pp_generic_association_aux pp_annot = function
  | AilGAtype (ty, e) ->
      pp_ctype no_qualifiers ty ^^ P.colon ^^^ pp_expression_aux pp_annot e
  | AilGAdefault e ->
      pp_keyword "default" ^^ P.colon ^^^ pp_expression_aux pp_annot e


let rec pp_statement_aux pp_annot (AnnotatedStatement (_, _, stmt)) =
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
                P.parens ( P.empty
                             (* TODO
                  P.optional (fun (dur, isRegister) ->
                    (fun z -> if isRegister then pp_keyword "register" ^^^ z else z)
                      (pp_storageDuration dur)
                  ) dur_reg_opt ^^^ pp_ctype_human qs ty
                ) ^^^ pp_id_obj id *) )
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
    | AilSwhile (e, s, _) ->
        pp_keyword "while" ^^^ P.parens (pp_expression_aux pp_annot e) ^^^ pp_statement s
    | AilSdo (s, e, _) ->
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
    | AilSlabel (l, s, _) ->
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
    | AilSreg_store (r, e) ->
        !^("r" ^ string_of_int r) ^^^ P.equals ^^^ pp_expression_aux pp_annot e ^^ P.semi

    | AilSpack (Annot.TPU_Predicate ident, es) ->
        !^ "__cerb_pack_struct" ^^^ Pp_symbol.pp_identifier ident ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi
    | AilSpack (Annot.TPU_Struct tag, es) ->
        !^ "__cerb_pack" ^^^ pp_id_type tag ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi
    | AilSunpack (Annot.TPU_Predicate ident, es) ->
        !^ "__cerb_unpack_struct" ^^^ Pp_symbol.pp_identifier ident ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi
    | AilSunpack (Annot.TPU_Struct tag, es) ->
        !^ "__cerb_unpack" ^^^ pp_id_type tag ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi
    | AilShave (ident, es) ->
      !^ "__cerb_have" ^^^ Pp_symbol.pp_identifier ident ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi
    | AilSshow (ident, es) ->
      !^ "__cerb_show" ^^^ Pp_symbol.pp_identifier ident ^^ P.parens (comma_list (pp_expression_aux pp_annot) es) ^^ P.semi


let pp_static_assertion pp_annot (e, lit) =
  pp_keyword "_Static_assert" ^^ P.parens (pp_expression_aux pp_annot e ^^ P.comma ^^^ pp_stringLiteral lit)


let pp_tag_definition (tag, (_, def)) =
  match def with
    | StructDef (ident_qs_tys, flexible_opt) ->
        pp_keyword "struct" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, (_, qs, ty)) ->
              pp_ctype qs ty ^^^ Pp_symbol.pp_identifier ident
            ) ident_qs_tys
          ) ^^ P.break 1 ^^
          P.optional (fun (FlexibleArrayMember (_, ident, qs, elem_ty)) ->
            pp_ctype qs (Ctype ([], Array (elem_ty, None))) ^^^ Pp_symbol.pp_identifier ident ^^ P.semi ^^ P.break 1
          ) flexible_opt        ) ^^ P.semi
    | UnionDef ident_qs_tys ->
        pp_keyword "union" ^^^ pp_id_type tag ^^^ P.braces (P.break 1 ^^
          P.nest 2 (
            P.separate_map (P.semi ^^ P.break 1) (fun (ident, (_, qs, ty)) ->
              pp_ctype qs ty ^^^ Pp_symbol.pp_identifier ident
            ) ident_qs_tys
          ) ^^ P.break 1
        ) ^^ P.semi

let pp_program_aux pp_annot (startup, sigm) =
(*  isatty := false; (*TODO: Unix.isatty Unix.stdout;*) *)
  (* Static assersions *)
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
  
  P.separate_map (P.break 1 ^^ P.hardline) (fun (sym, (_, _, decl)) ->
    match decl with
      | Decl_object (sd, qs, ty) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          pp_ansi_format [Red] (!^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ (pp_ctype_human qs ty)) ^^
          P.hardline ^^
          
          (if !Debug_ocaml.debug_level > 5 then
            (* printing the types in a human readable format *)
            pp_id_obj sym ^^ P.colon ^^^ P.parens (pp_ctype_human qs ty)
          else
            pp_ctype_declaration (pp_id_obj sym) qs ty) ^^
          
          P.optional (fun e ->
            P.space ^^ P.equals ^^^ pp_expression_aux pp_annot e
          ) (List.assoc_opt sym sigm.object_definitions) ^^ P.semi
      
      | Decl_function (has_proto, (ret_qs, ret_ty), params, is_variadic, is_inline, is_Noreturn) ->
          (* first pprinting in comments, some human-readably declarations *)
          (* TODO: colour hack *)
          pp_ansi_format [Red] (
            !^ "// declare" ^^^ pp_id sym ^^^
            (if has_proto then !^ "WITH PROTO " else P.empty) ^^
            !^ "as" ^^^ pp_ctype_human no_qualifiers (Ctype ([], Function ((ret_qs, ret_ty), params, is_variadic)))
          ) ^^ P.hardline ^^
          
          (fun k -> if is_inline   then !^ "inline"    ^^^ k else k) (
            (fun k -> if is_Noreturn then !^ "_Noreturn" ^^^ k else k) (
              begin
                if !Debug_ocaml.debug_level > 5 then
                  (* printing the types in a human readable format *)
                  pp_ctype_human ret_qs ret_ty ^^^ pp_id_func sym
                else
                  pp_ctype_declaration (pp_id_func sym) ret_qs ret_ty
              end ^^
              (match List.assoc_opt sym sigm.function_definitions with
                | Some (_, _, param_syms, stmt) ->
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




let rec pp_genIntegerType = function
  | Concrete ity ->
      pp_integerType ity
  | SizeT ->
      !^ "size_t"
  | PtrdiffT ->
      !^ "ptrdiff_t"
  | VaddrT ->
      !^ "vaddr_t"
  | Unknown iCst ->
      !^ "unknown constant" ^^^ P.brackets (pp_integerConstant iCst)
  | Promote gity ->
      !^ "integer promotion of" ^^^ P.brackets (pp_genIntegerType gity)
  | Usual (gity1, gity2) ->
      !^ "usual arithmetic conversions with type" ^^^ P.brackets (pp_genIntegerType gity1 ^^^ !^"and" ^^^ pp_genIntegerType gity2)

let pp_genBasicType = function
  | GenInteger gity ->
      pp_genIntegerType gity
  | GenFloating fty ->
      pp_floatingType fty

let pp_genType = function
  | GenVoid ->
      !^ "void"
  | GenBasic gbty ->
      pp_genBasicType gbty
  | GenArray (ty, n_opt) ->
      !^ "array" ^^^ P.optional pp_integer n_opt ^^^ !^ "of" ^^^ pp_ctype no_qualifiers ty
  | GenFunction ((qs, ty), params, is_variadic) ->
      (* TODO: maybe add parameters *)
      !^ "function returning" ^^^ pp_ctype qs ty
  | GenFunctionNoParams (qs, ty) ->
      !^ "function (NO PARAMS) returning" ^^^ pp_ctype qs ty
  | GenPointer (ref_qs, ref_ty) ->
      pp_ctype no_qualifiers (Ctype ([], Pointer (ref_qs, ref_ty)))
  | GenStruct tag_sym ->
      !^ "struct" ^^^ pp_id tag_sym
  | GenUnion tag_sym ->
      !^ "union" ^^^ pp_id tag_sym
  | GenAtomic ty ->
      !^ "atomic" ^^^ pp_ctype no_qualifiers ty

let pp_genTypeCategory = function
 | GenLValueType (qs, ty, isRegister) ->
     !^ "GenLValueType" ^^ P.brackets (
       pp_qualifiers qs ^^ P.comma ^^^ pp_ctype_raw ty ^^ P.comma ^^^ !^ (if isRegister then "true" else "false")
     )
 | GenRValueType gty ->
     !^ "GenRValueType" ^^ P.brackets (pp_genType gty)

let pp_expression e = pp_expression_aux (fun _ d -> d) e
let pp_generic_association ga = pp_generic_association_aux (fun _ d -> d) ga
let pp_statement s = pp_statement_aux (fun _ d -> d) s



let _pp_annot gtc doc =
  match gtc with
    | GenLValueType (qs, ty, isRegister) ->
        failwith "WIP"
    | GenRValueType gty ->
        P.parens (!^ "/*" ^^^ pp_genType gty ^^^ !^ "*/" ^^^ doc)

let filter_external_decl (id, sigma) =
  let pred (_, (loc, _, _)) = Location_ocaml.from_main_file loc in
  (id, { sigma with declarations = List.filter pred sigma.declarations} )

let pp_program do_colour show_include ail_prog =
  Colour.do_colour := do_colour && Unix.isatty Unix.stdout;
  let filtered_ail_prog = if show_include then ail_prog else filter_external_decl ail_prog in
  pp_program_aux (fun _ doc -> doc) filtered_ail_prog

(* For debugging: prints all the type annotations *)
let pp_program_with_annot =
  pp_program_aux (fun gtc doc -> P.braces (pp_genTypeCategory gtc) ^^ P.brackets doc)


let pp_id_only (Symbol.Identifier (_,n)) = P.string n
let pp_attr_arg (_, arg, _) = P.dquotes (P.string arg)
let pp_attr_args args = P.parens (P.separate_map P.comma pp_attr_arg args)


let pp_attribute a = 
  P.optional (fun ns -> pp_id_only ns ^^ P.colon ^^ P.colon) a.Annot.attr_ns  ^^ 
    pp_id_only a.Annot.attr_id ^^^ pp_attr_args a.Annot.attr_args

let pp_attributes (Annot.Attrs attrs) = 
  match attrs with
  | [] -> P.empty
  | _ -> P.brackets (P.brackets (P.separate_map P.comma pp_attribute attrs))
