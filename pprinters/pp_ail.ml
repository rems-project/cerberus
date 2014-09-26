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
  | AilEunary (PostfixIncr, _)
  | AilEunary (PostfixDecr, _) -> Some 1

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

let rec pp_ctype = function
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      !^ "void"
  | Basic  b ->
      pp_basicType b
  | Array (ty, n) ->
      pp_ctype ty ^^ P.brackets (pp_integer n)
  | Function (ty, ps, is_variadic) ->
      pp_ctype ty ^^ P.parens (
        let p = comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype t)) ps in
        if is_variadic then
          p ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
        else
          p
      )
  | Pointer (qs, ty) ->
      pp_qualifiers qs (pp_ctype ty ^^ P.star)
  | Atomic ty ->
      !^ "_Atomic" ^^ P.parens (pp_ctype ty)
  | Struct (tag, ident_tys) ->
      !^ "struct" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
  | Union (tag, ident_tys) ->
      !^ "union" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)


let rec pp_ctype_declaration id = function
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      !^ "void" ^^^ id
  | Basic  b ->
      pp_basicType b ^^^ id
  | Array (ty, n) ->
      pp_ctype ty ^^^ id ^^ P.brackets (pp_integer n)
  | Function (ty, ps, is_variadic) ->
      pp_ctype_declaration id ty ^^ P.parens (
        let p = comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype t)) ps in
        if is_variadic then
          p ^^ P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
        else
          p
      )
  | Pointer (qs, ty) ->
      pp_qualifiers qs (pp_ctype ty ^^^ P.star ^^ id)
  | Atomic ty ->
      !^ "_Atomic" ^^ P.parens (pp_ctype ty)
  | Struct (tag, ident_tys) ->
      !^ "struct" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys) ^^^ id
  | Union (tag, ident_tys) ->
      !^ "union" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys) ^^^ id


(* pprint C types in human readable format *)
let rec pp_ctype_human = function
(*  let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  | Void ->
      !^ "void"
  | Basic  b ->
      pp_basicType b
  | Array (ty, n) ->
      !^ "array" ^^^ pp_integer n ^^^ !^ "of" ^^^ pp_ctype_human ty
  | Function (ty, ps, is_variadic) ->
      !^ (if is_variadic then "variadic function" else "function") ^^^
      P.parens (comma_list (fun (q,t) -> pp_qualifiers q (pp_ctype_human t)) ps) ^^^
      !^ "returning" ^^^ pp_ctype_human ty
  | Pointer (qs, ty) ->
      pp_qualifiers qs (!^ "pointer to" ^^^ pp_ctype_human ty)
  | Atomic ty ->
      !^ "atomic" ^^^ pp_ctype_human ty
  | Struct (tag, ident_tys) ->
      !^ "struct" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype_human ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)
  | Union (tag, ident_tys) ->
      !^ "union" ^^^ pp_id tag ^^^
      P.braces (comma_list (fun (ident, ty) -> pp_ctype_human ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys)








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
    | LL  -> "LL"
  in
  fun z -> P.string (to_string z)

(*
let rec string_of_octal_big_int n =
  let (n', r) = Big_int.quomod_big_int n in
  match r with
    | 
 *)

let string_of_big_int_with_basis n b =
  let char_of_digit = function
      | 15 -> 'f'
      | 14 -> 'e'
      | 13 -> 'd'
      | 12 -> 'c'
      | 11 -> 'b'
      | 10 -> 'a'
      | r  -> char_of_int (r + 48) in
  let rec f n acc =
    let (n', r) = Big_int.quomod_big_int n b in
    let c = char_of_digit (Big_int.int_of_big_int r) in
    if Big_int.eq_big_int n' Big_int.zero_big_int then
      c :: acc
    else
      f n' (c :: acc) in
  f n []

let string_of_octal_big_int n =
  if Big_int.eq_big_int n Big_int.zero_big_int then
    "0"
  else
    let l = string_of_big_int_with_basis n (Big_int.big_int_of_int 8) in
    let ret = String.create (List.length l+1) in
    ret.[0] <- '0';
    List.iteri (fun i c ->
      ret.[i+1] <- c
    ) l;
    ret

let string_of_hexadecimal_big_int n =
  let l = string_of_big_int_with_basis n (Big_int.big_int_of_int 16) in
  let ret = String.create (List.length l + 2) in
  ret.[0] <- '0';
  ret.[1] <- 'x';
  List.iteri (fun i c ->
    ret.[i+2] <- c
  ) l;
  ret



(* TODO: should reverse the decoding of n *)
let pp_integerConstant (n, basis, suff_opt) =
  !^ (match basis with
    | Octal       -> string_of_octal_big_int n
    | Decimal     -> Big_int.string_of_big_int n
    | Hexadecimal -> string_of_hexadecimal_big_int n
  )  ^^ (P.optional pp_integerSuffix suff_opt)


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

let pp_stringLiteral (pref_opt, str) =
  (P.optional pp_encodingPrefix pref_opt) ^^ P.dquotes (!^ str)


let rec pp_constant = function
  | ConstantIndeterminate ty ->
      !^ "indet" ^^ P.parens (pp_ctype ty)
  | ConstantNull ->
      !^ "NULL"
  | ConstantInteger ic ->
      pp_integerConstant ic
  | ConstantCharacter cc ->
      pp_characterConstant cc
 | ConstantArray csts ->
     P.braces (comma_list pp_constant csts)
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




let rec pp_expression a_expr =
  let rec pp p (AnnotatedExpression (_, expr)) =
    let p' = precedence expr in
    let pp z = P.group (pp p' z) in
    (if lt_precedence p' p then fun z -> z else P.parens)
      (match expr with
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
            pp_qualifiers qs (P.parens (pp_ctype ty)) ^^^ pp e
        | AilEcall (e, es) ->
            pp e ^^ P.parens (comma_list pp es)
        | AilEgeneric (e, gas) ->
            !^ "_Generic" ^^ P.parens (pp e ^^ P.comma ^^^ comma_list pp_generic_association gas)
        | AilEstr lit ->
            pp_stringLiteral lit
        | AilEconst c ->
            pp_constant c
        | AilEident x ->
            pp_id x
        | AilEsizeof (qs, ty) ->
            !^ "sizeof" ^^ P.parens (pp_qualifiers qs (pp_ctype ty))
        | AilEalignof (qs, ty) ->
            !^ "_Alignof" ^^ P.parens (pp_qualifiers qs (pp_ctype ty))

        | AilEmemberof (e, ident) ->
            pp e ^^ P.dot ^^ Pp_cabs.pp_cabs_identifier ident
        | AilEmemberofptr (e, ident) ->
            pp e ^^ (!^ "->") ^^ Pp_cabs.pp_cabs_identifier ident
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
      ) in
  pp None a_expr

and pp_generic_association = function
  | AilGAtype (ty, e) ->
      pp_ctype ty ^^ P.colon ^^^ pp_expression e
  | AilGAdefault e ->
      !^ "default" ^^ P.colon ^^^ pp_expression e



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
    | AilSskip ->
        P.semi
    | AilSexpr e ->
        pp_expression e ^^ P.semi
    | AilSblock (ids, ss) ->
        let block =
          P.separate_map
            (P.semi ^^ P.break 1)
            (fun (id, (qs, ty)) -> pp_qualifiers qs (pp_ctype ty) ^^^ pp_id id)
            ids ^^ P.semi ^^
          P.break 1 ^^
          P.separate_map (P.break 1) pp_statement ss in
        P.lbrace ^^ P.nest 2 (P.break 1 ^^ block) ^/^ P.rbrace
    | AilSif (e, s1, s2) ->
        !^ "if" ^^^ P.parens (pp_expression e) ^/^
          P.nest 2 (pp_statement s1) ^^^
        !^ "else" ^/^
          pp_statement s2
    | AilSwhile (e, s) ->
        !^ "while" ^^^ P.parens (pp_expression e) ^^^ pp_statement s
    | AilSdo (s, e) ->
        !^ "do" ^^^ pp_statement s ^^^ !^ "while" ^^^ P.parens (pp_expression e)
    | AilSbreak ->
        !^ "break" ^^ P.semi
    | AilScontinue ->
        !^ "continue" ^^ P.semi
    | AilSreturnVoid ->
        !^ "return" ^^ P.semi
    | AilSreturn e ->
        !^ "return" ^^^ pp_expression e ^^ P.semi
    | AilSswitch (e, s) ->
        !^ "switch" ^^^ P.parens (pp_expression e) ^/^ pp_statement s
    | AilScase (ic, s) ->
        !^ "case" ^^^ pp_integerConstant ic ^^ P.colon ^/^ pp_statement s
    | AilSdefault s ->
        !^ "default" ^^ P.colon ^/^ pp_statement s
    | AilSlabel (l, s) ->
        pp_id l ^^ P.colon ^/^ pp_statement s
    | AilSgoto l ->
        !^ "goto" ^^^ pp_id l ^^ P.semi
    (* TODO: looks odd *)
    | AilSdeclaration defs ->
        comma_list (fun (id, e) -> pp_id id ^^^ P.equals ^^^ pp_expression e) defs ^^
        P.semi ^^^ !^ "// decl"




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





let pp_static_assertion (e, lit) =
  !^ "_Static_assert" ^^ P.parens (pp_expression e ^^ P.comma ^^^ pp_stringLiteral lit)

let pp_program (startup, sigm) =
  P.separate_map (P.break 1) pp_static_assertion sigm.static_assertions ^^ P.break 1 ^^
  
  List.fold_left (fun acc (sym, decl) ->
    match decl with
      | Decl_object (qs, ty) ->
          (* first pprinting in comments, some human-readably declarations *)
          !^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ (pp_qualifiers qs (pp_ctype_human ty)) ^^ P.hardline ^^
          
          (pp_qualifiers qs (pp_ctype_declaration (pp_id sym) ty)) ^^^
          P.optional (fun e ->
            P.equals ^^^ pp_expression e
          ) (Context.lookup eq_identifier sigm.object_definitions sym) ^^ P.semi ^^
          P.break 1 ^^ P.hardline ^^ acc
      
      | Decl_function (return_ty, params, is_variadic, is_inline, is_Noreturn) ->
          (* first pprinting in comments, some human-readably declarations *)
          !^ "// declare" ^^^ pp_id sym ^^^ !^ "as" ^^^ pp_ctype_human (Function (return_ty, params, is_variadic)) ^^ P.hardline ^^
          
          (fun k -> if is_inline   then !^ "inline"    ^^^ k else k) (
            (fun k -> if is_Noreturn then !^ "_Noreturn" ^^^ k else k) (
              pp_ctype_declaration (pp_id sym) return_ty ^^
              (match Context.lookup eq_identifier sigm.function_definitions sym with
                | Some (param_syms, stmt) ->
                    P.parens (
                      comma_list (fun (sym, (qs, ty)) ->
                        (pp_qualifiers qs (pp_ctype ty)) ^^^ pp_id sym
                      ) (List.combine param_syms params) ^^
                      if is_variadic then
                        P.comma ^^^ P.dot ^^ P.dot ^^ P.dot
                      else
                        P.empty
                    ) ^^^
                    pp_statement stmt
                | None ->
                    P.parens (
                      comma_list (fun (qs, ty) ->
                        pp_qualifiers qs (pp_ctype ty)
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
