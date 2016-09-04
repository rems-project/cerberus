(* Created by Victor Gomes 2016-01-19 *)
(* It generates an Ocaml file from Core AST *)

open Util
open Pp_prelude
open Core
open AilTypes
open Defacto_memory_types
open Core_ctype
open CodegenAux

exception Unsupported
exception Type_expected of core_base_type

let ( ^//^ ) x y = x ^^ P.break 1 ^^ P.break 1 ^^ y
let ( !> ) x = P.nest 2 (P.break 1 ^^ x)

(* String helper function *)
let string_tr target replace str =
  String.map (fun c -> if c = target then replace else c) str

(* Print TODO *)
let todo str = !^"raise (A.Error " ^^ !^str ^^ !^")"

(* Extend pretty printer *)
let print_comment doc = P.parens (P.star ^^^ doc ^^^ P.star)

let print_if b x y =
  !^"if" ^^^ b ^^^ !^"then (" ^^ !> x ^/^ !^") else (" ^^ !> y ^/^ !^")"

let print_let r p x y =
  !^"let" ^^ (if r then !^" rec" else P.empty) ^^^ p ^^^ P.equals ^^^ x
  ^^^ !^"in" ^/^ !> y

let print_seq p x y = x ^^ !> (!^">>= fun" ^^^ p ^^ !^" ->") ^/^ y

let print_bool b = if b then !^"true" else !^"false"

let print_option_type pp = function
  | Some e  -> !^"Some" ^^^ P.parens (pp e)
  | None    -> !^"None"

(* Print symbols (variables name, function names, etc...) *)
let print_symbol a = !^(Pp_symbol.to_string_pretty a)

let print_raw_symbol = function
  | Symbol.Symbol (i, None)     ->
    !^"Symbol.Symbol" ^^^ P.parens (!^(string_of_int i) ^^ P.comma ^^^ !^"None")
  | Symbol.Symbol (i, Some str) ->
    !^"Symbol.Symbol" ^^^ P.parens (!^(string_of_int i) ^^ P.comma
                                    ^^^ !^"Some" ^^^ P.dquotes !^str)

(* Take out all '.' and add 'impl_' as prefix *)
let print_impl_name i = !^("_"
  ^ (string_tr '.' '_' (Implementation_.string_of_implementation_constant i)))

(* It was print an unknown location *)
let print_cabs_id (Cabs.CabsIdentifier (_, str)) =
  !^("Cabs.CabsIdentifier (Location_ocaml.unknown, " ^ str ^ ")")

let print_list pp xs =
  let rec print_elem xs =
    match xs with
    | [] -> P.empty
    | [x] -> pp x
    | x :: xs -> pp x ^^ P.semi ^^^ (print_elem xs)
  in !^"[" ^^ print_elem xs ^^ !^"]"

let print_name = function
  | Sym a  -> print_symbol a
  | Impl i -> print_impl_name i

(* Printing types *)
let rec print_core_object = function
 | OTy_integer    -> !^"M.integer_value0"
 | OTy_floating   -> !^"M.floating_value0"
 | OTy_pointer    -> !^"M.pointer_value0"
 | OTy_cfunction  -> !^"M.pointer_value0" (* cfunction is a pointer value? *)
                       (*TODO: I am not sure about these: *)
 | OTy_array obj  -> !^"[" ^^ print_core_object obj ^^ !^"]"
 | OTy_struct sym -> !^"struct" ^^^ print_symbol sym
 | OTy_union sym  -> !^"union" ^^^ print_symbol sym

let rec print_base_type = function
  | BTy_unit       -> !^"()"
  | BTy_boolean    -> !^"bool"
  | BTy_ctype      -> !^"C.ctype0"
  | BTy_list bTys  -> P.parens (print_base_type bTys) ^^^ !^"list"
  | BTy_tuple bTys -> P.parens (P.separate_map P.star print_base_type bTys)
  | BTy_object obj -> print_core_object obj
  | BTy_loaded obj -> P.parens (print_core_object obj)  ^^^ !^"A.loaded"

let print_core_type = function
  | TyBase   baseTy -> print_base_type baseTy
  | TyEffect baseTy -> print_base_type baseTy

(* Binary operations and precedences *)

(* FIXME: test if t1 and t2 are the same up to loaded *)
(* TODO: all the binops case *)
let print_binop binop pp (Pexpr (t1, pe1_) as pe1) (Pexpr (t2, pe2_) as pe2) =
  match binop with
  | OpAdd -> !^"(M.op_ival0 M.IntAdd (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpSub -> !^"(M.op_ival0 M.IntSub (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpMul -> !^"(M.op_ival0 M.IntMul (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpDiv -> !^"(M.op_ival0 M.IntDiv (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpRem_t -> !^"(M.op_ival0 M.IntRem_t (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpRem_f -> !^"(M.op_ival0 M.IntRem_f (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpExp -> !^"(M.op_ival0 M.IntExp (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
  | OpEq  -> (
      match t1 with
      | BTy_object (OTy_integer)
      | BTy_loaded (OTy_integer) ->
        !^"A.eq" ^^^ P.parens (pp pe1) ^^^ P.parens (pp pe2)
        (*!^"(O.get (M.eq_ival0 M.initial_mem_state0 Symbolic.Constraints_TODO  ("
          ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^")))"*)
      | BTy_object (OTy_pointer)
      | BTy_loaded (OTy_pointer) ->
        !^"(M.eq_ptrval0 Symbolic.Constraints_TODO  (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^"))"
      | BTy_ctype ->
        !^"(C.ctypeEqual0 (" ^^ pp pe1 ^^ !^") (" ^^ pp pe2 ^^ !^"))"
      | _ -> todo "binop eq"
    )
  | OpLt  -> (
      match t1 with
      | BTy_object (OTy_integer)
      | BTy_loaded (OTy_integer) ->
        !^"A.lt" ^^^ P.parens (pp pe1) ^^^  P.parens (pp pe2)
        (*
        !^"(O.get (M.lt_ival0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"*)
      | BTy_object (OTy_pointer)
      | BTy_loaded (OTy_pointer) ->
        !^"(O.get (M.lt_ptrval0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"
      | _ -> todo "binop lt"
    )
  | OpLe  -> (
      match t1 with
      | BTy_object (OTy_integer)
      | BTy_loaded (OTy_integer) ->
        !^"A.le" ^^^ P.parens (pp pe1) ^^^  P.parens (pp pe2)
       (* !^"(O.get (M.le_ival0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"*)
      | BTy_object (OTy_pointer)
      | BTy_loaded (OTy_pointer) ->
        !^"(O.get (M.le_ptrval0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"
      | _ -> todo "binop lt"
    )
  | OpGt  -> (
      match t1 with
      | BTy_object (OTy_integer)
      | BTy_loaded (OTy_integer) ->
        !^"A.gt" ^^^ P.parens (pp pe1) ^^^  P.parens (pp pe2)
        (*!^"(O.get (M.gt_ival0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"*)
      | BTy_object (OTy_pointer)
      | BTy_loaded (OTy_pointer) ->
        !^"(O.get (M.gt_ptrval0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"
      | _ -> todo "binop gt"
    )
  | OpGe  -> (
      match t1 with
      | BTy_object (OTy_integer)
      | BTy_loaded (OTy_integer) ->
        !^"A.ge" ^^^ P.parens (pp pe1) ^^^  P.parens (pp pe2)
        (*!^"(O.get (M.ge_ival0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"*)
      | BTy_object (OTy_pointer)
      | BTy_loaded (OTy_pointer) ->
        !^"(O.get (M.ge_ptrval0 Symbolic.Constraints_TODO (" ^^ pp pe1 ^^ !^") ("
          ^^ pp pe2 ^^ !^")))"
      | _ -> todo "binop ge"
    )
  | OpAnd -> pp pe1 ^^^ !^" && " ^^^ pp pe2
  | OpOr  -> pp pe1 ^^^ !^ "||" ^^^ pp pe2

let binop_precedence (Pexpr (_, pe)) = match pe with
  | PEop (OpExp, _, _) -> Some 1
  | PEop (OpMul, _, _)
  | PEop (OpDiv, _, _)
  | PEop (OpRem_t, _, _)
  | PEop (OpRem_f, _, _) -> Some 2
  | PEop (OpAdd, _, _)
  | PEop (OpSub, _, _) -> Some 3
  | PEop (OpLt,  _, _)
  | PEop (OpLe,  _, _) -> Some 4
  | PEop (OpGt,  _, _)
  | PEop (OpGe,  _, _) -> Some 4
  | PEop (OpEq,  _, _) -> Some 5
  | PEop (OpAnd, _, _) -> Some 6
  | PEop (OpOr,  _, _) -> Some 7
  | _ -> None

let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true

(* Print let expression patterns *)

(* These will not really match *)
let rec print_pattern = function
  | CaseBase (None, _) -> P.underscore
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (ctor, pas) -> print_match_ctor (match pas with
    | []   -> P.underscore
    | [pa] -> print_pattern pa
    | _    -> P.parens (comma_list print_pattern pas)) ctor
and print_match_ctor arg = function
  | Cnil _       -> !^"[]"
  | Ccons        -> !^"Cons"
  | Ctuple       -> arg
  | Carray       -> !^"array"
  | Civmax       -> !^"A.ivmax"
  | Civmin       -> !^"A.ivmin"
  | Civsizeof    -> !^"M.sizeof_ival0"
  | Civalignof   -> !^"M.alignof_ival0"
  | Cspecified   -> !^"A.Specified" ^^ P.parens arg
  | Cunspecified -> !^"A.Unspecified" ^^ P.parens arg

let print_match pe pp pas =
  !^"match" ^^^ pe ^^^ !^"with" ^^ !> (List.fold_right (
      fun (pat, pe) acc -> !^"|" ^^^print_pattern pat ^^^ !^"->" ^^^ pp pe ^/^ acc
    ) pas P.empty)

let print_nat_big_num n =
  !^"Nat_big_num.of_string" ^^^ P.dquotes (!^(Nat_big_num.to_string n))

let print_symbol_prefix = function
  | Symbol.PrefSource syms ->
    !^"Symbol.PrefSource" ^^^ print_list print_raw_symbol syms
  | Symbol.PrefOther str   ->
    !^"Symbol.PrefOther" ^^^ P.dquotes !^str

(* TODO: Int_leastN_t *)
let print_ail_integer_base_type = function
  | Ichar          -> !^"T.Ichar"
  | Short          -> !^"T.Short"
  | Int_           -> !^"T.Int_"
  | Long           -> !^"T.Long"
  | LongLong       -> !^"T.LongLong"
   (* Things defined in the standard libraries *)
  | IntN_t n       -> !^"T.IntN_t" ^^^ !^(string_of_int n)
  | Int_leastN_t n -> !^"T.Int_leastN_t" ^^^ todo "int_leastnt"
  | Int_fastN_t n  -> !^"T.Int_fastN_t" ^^^ todo "int+fastnt"
  | Intmax_t       -> !^"T.Intmax_t"
  | Intptr_t       -> !^"T.Intptr_t"

let print_ail_integer_type = function
  | Char         -> !^"T.Char"
  | Bool         -> !^"T.Bool"
  | Signed ibt   -> !^"T.Signed" ^^^ P.parens (print_ail_integer_base_type ibt)
  | Unsigned ibt -> !^"T.Unsigned" ^^^ P.parens (print_ail_integer_base_type ibt)
  | IBuiltin str -> !^"T.IBuiltin" ^^^ !^str
  | Enum ident   -> !^"T.Enum" ^^^ P.parens (print_symbol ident)
  | Size_t       -> !^"T.Size_t"
  | Ptrdiff_t    -> !^"T.Ptrdiff_t"

let print_integer_value_base = function
  | IVconcrete bignum             ->
    !^"I.IVconcrete" ^^^ P.parens (print_nat_big_num bignum)
  | IVaddress (Address0 (sym, n))  ->
    !^"I.IVAddress" ^^^ P.parens (!^"I" ^^^ P.parens (print_symbol_prefix sym
                                   ^^ P.comma ^^^ !^(string_of_int n)))
  | IVmax ait                     -> !^"I.IVmax" ^^^ P.parens
                                       (print_ail_integer_type ait)
  | IVmin ait                     -> !^"I.IVmin" ^^^ P.parens
                                       (print_ail_integer_type ait)
  | IVunspecified                 -> !^"I.IVunspecified"
  | IVop (op, ivs)                -> raise Unsupported
  | IVsizeof cty                  -> raise Unsupported
  | IValignof cty                 -> raise Unsupported
  | IVoffsetof (sym, cabs_id)     -> raise Unsupported
  | IVbyteof (ivb, mv)            -> raise Unsupported
  | IVcomposite ivs               -> raise Unsupported
  | IVfromptr (ivb, mv)           -> raise Unsupported
  | IVptrdiff (ivb, mv)           -> raise Unsupported
  | IVconcurRead (_, _)           -> raise Unsupported

let print_ail_qualifier {
  AilTypes.const = c;
  AilTypes.restrict = r;
  AilTypes.volatile = v;
  AilTypes.atomic = a;
} = !^"{" ^^ P.nest 2 (P.break 1 ^^
    !^"T.const = " ^^ print_bool c ^^ !^";" ^/^
    !^"T.restrict = " ^^ print_bool r ^^ !^";" ^/^
    !^"T.volatile = " ^^ print_bool v ^^ !^";" ^/^
    !^"T.atomic = " ^^ print_bool a ^^ !^";"
    ) ^^ P.break 1 ^^ !^"}"

let print_ail_basic_type = function
  | Integer it  -> !^"T.Integer" ^^^ P.parens (print_ail_integer_type it)
  | Floating ft -> todo "floating type"

let rec print_ctype = function
  | Void0 -> !^"C.Void0"
  | Basic0 abt ->
    !^"C.Basic0" ^^^ P.parens (print_ail_basic_type abt)
  | Array0 (cty, num) ->
    !^"C.Array0" ^^^ P.parens (print_ctype cty ^^ P.comma
                               ^^^ print_option_type print_nat_big_num num)
  | Function0 (cty, params, variad) ->
    !^"C.Function0" ^^^ P.parens
      (print_ctype cty ^^ P.comma ^^^ print_list
         (fun (q, cty) -> print_ail_qualifier q ^^ P.comma ^^^ print_ctype cty)
         params
       ^^ P.comma ^^^ print_bool variad)
  | Pointer0 (q, cty) ->
    !^"C.Pointer0" ^^^ P.parens (print_ail_qualifier q ^^ P.comma ^^^ print_ctype cty)
  | Atomic0 cty -> !^"C.Atomic0" ^^^ P.parens (print_ctype cty)
  | Struct0 strct -> !^"C.Struct0" ^^^ P.parens (print_raw_symbol strct)
  | Union0 union -> !^"C.Union0" ^^^ P.parens (print_raw_symbol union)
  | Builtin0 str -> !^"C.Builtin0" ^^^ !^str

let print_provenance = function
  | Prov_wildcard -> !^"I.Prov_wildcard"
  | Prov_none     -> !^"I.Prov_none"
  | Prov_device   -> !^"I.Prov_device"
  | Prov_some ids -> todo "prov_some"

let print_iv_value = function
  | IV (Prov_none, IVconcrete n) -> !^"A.mk_int" ^^^ P.dquotes (!^(Nat_big_num.to_string n))
  | IV (prov, ivb) -> !^"I.IV" ^^^ P.parens (print_provenance prov ^^ P.comma
                                             ^^^ print_integer_value_base ivb)

let rec print_pointer_value_base = function
  | PVnull cty        -> !^"I.PVnull" ^^^ P.parens (print_ctype cty)
  | PVfunction sym    -> !^"I.PVfunction" ^^^ P.parens (print_symbol sym)
  | PVbase (id, pre)  -> !^"I.PVbase" ^^^ P.parens (!^(string_of_int id) ^^ P.comma
                                                    ^^^ print_symbol_prefix pre)
  | PVfromint ivb     -> !^"I.PVfromint" ^^^ P.parens (print_integer_value_base ivb)
  | PVunspecified cty -> !^"I.PVunspecified" ^^^ P.parens (print_ctype cty)

and print_shift_path_element = function
  | SPE_array (cty, ivb)  ->
    !^"I.SPE_array" ^^^ P.parens (print_ctype cty ^^ P.comma
                                  ^^^ print_integer_value_base ivb)
  | SPE_member (_, _)     -> todo "spe member"

and print_shift_path sp = print_list print_shift_path_element sp

and print_pointer_value = function
  | PV (p, pvb, sp) ->
    !^"I.PV" ^^^ P.parens (print_provenance p ^^ P.comma
                           ^^^ print_pointer_value_base pvb ^^ P.comma
                           ^^^ print_shift_path sp)

let print_floating_value = function
  | FVunspecified   -> !^"I.FVunspecified"
  | FVconcrete str  -> !^"I.FVconcrete" ^^^ !^str

let rec print_object_value = function
  | OVstruct _
  | OVunion  _     -> todo "print_obj_value"
  | OVcfunction nm -> print_name nm
  | OVinteger iv   -> print_iv_value iv
  | OVfloating fv  -> print_floating_value fv
  | OVpointer pv   -> print_pointer_value pv
  | OVarray obvs   -> print_list print_object_value obvs

let rec print_mem_value = function
  | MVinteger (ait, iv) -> !^"I.MVinteger" ^^ P.parens
                             (print_ail_integer_type ait ^^ P.comma ^^^ print_iv_value iv)
  | MVfloating _        -> todo "mvfloating"
  | MVpointer (cty, pv) -> !^"I.MVpointer" ^^ P.parens
                             (print_ctype cty ^^P.comma ^^^ print_pointer_value pv)
  | MVarray mvs         -> !^"I.MVarray" ^^^ print_list print_mem_value mvs
  | MVstruct (sym, sls) -> !^"I.MVstruct" ^^^ print_list
                             (fun (cid, mv) -> P.parens (print_cabs_id cid ^^ P.comma
                                                         ^^^ print_mem_value mv)) sls
  | MVunion (sym,cid,mv) -> !^"I.MVunion" ^^^ P.parens
                             (print_symbol sym ^^ P.comma ^^^ print_cabs_id cid
                              ^^ P.comma ^^^ print_mem_value mv)

(* Print type values *)
let rec print_value = function
  | Vunit            -> P.parens P.empty
  | Vtrue            -> !^"true"
  | Vfalse           -> !^"false"
  | Vlist (_, cvals) -> print_list print_value cvals
  | Vtuple cvals     -> P.parens (comma_list print_value cvals)
  | Vctype ty        -> print_ctype ty
  | Vunspecified ty  -> !^"A.Unspecified" ^^^ P.parens (print_ctype ty)
  | Vobject obv      -> print_object_value obv
  | Vconstrained _   -> todo "vconstrained"
  | Vspecified v     -> !^"A.Specified" ^^^ P.parens (print_object_value v)
                          (* TODO: it shouldn't be possible v evaluates to IVunspecified *)


(* Print expressions (pure and eff) *)
let print_pure_expr pe =
  let rec pp prec pe =
    let prec' = binop_precedence pe in
    let pp z  = P.group (pp prec' z) in
    (if lt_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with Pexpr (t, pe') ->
      match pe' with
      | PEsym sym -> print_symbol sym
      | PEimpl iCst -> print_impl_name iCst ^^^ P.parens P.space
      | PEval cval -> print_value cval
      | PEconstrained _ -> todo "peconstrained"
      | PEundef ub ->
        !^"raise" ^^^ P.parens (
          !^"A.Undefined" ^^^ P.dquotes
            (!^(Undefined.stringFromUndefined_behaviour ub))
        )
      | PEerror (str, pe) ->
        !^"raise" ^^^ !^"(A.Error" ^^^ P.dquotes (!^str ^^^ pp pe) ^^ !^")"
      | PEctor (ctor, pes) ->
          let pp_args sep = P.parens (P.separate_map sep (fun x -> P.parens (pp x)) pes) in
          begin
          match ctor with
          | Cnil _ -> !^"[]"
          | Ccons ->
            (match pes with
             | []       -> raise (CodegenAux.Error "Ccons: empty list")
             | [pe]     -> !^"[" ^^ pp pe ^^ !^"]"
             | [pe;pes] -> pp pe ^^^ !^"::" ^^^ pp pes
             | _        -> raise (CodegenAux.Error "Ccons: more than 2 args")
            )
          | Ctuple       -> pp_args P.comma
          | Carray       -> !^"array"
          | Civmax       -> !^"A.ivmax" ^^^ pp_args P.space
          | Civmin       -> !^"A.ivmin" ^^^ pp_args P.space
          | Civsizeof    -> !^"M.sizeof_ival0" ^^^ pp_args P.space
          | Civalignof   -> !^"M.alignof_ival0" ^^^ pp_args P.space
          | Cspecified   -> !^"A.Specified" ^^^ pp_args P.space
          | Cunspecified -> !^"A.Unspecified"  ^^^ pp_args P.space
          end
      | PEcase (pe, pas) -> print_match (pp pe) pp pas
      | PEarray_shift (pe1, ty, pe2) -> 
        !^"(M.array_shift_ptrval0 (" ^^ pp pe1 ^^ !^") ("
          ^^ print_ctype ty ^^ !^") (" ^^ pp pe2 ^^ !^"))"
      | PEmember_shift (pe, tag_sym, memb_ident) -> todo "pure: member_shift"
      | PEnot pe -> !^"not" ^^^ P.parens (pp pe)
      | PEop (bop, pe1, pe2) -> print_binop bop pp pe1 pe2
      | PEstruct _ -> todo "struct"
      | PEunion _ -> todo "union"
      | PEcall (nm, pes) -> 
        print_name nm ^^^ (
          if List.length pes = 0
          then P.parens P.empty
          else P.separate_map P.space (fun (Pexpr (t, x)) ->
              match x with
              | (PEsym sym) -> pp (Pexpr (t, PEsym sym))
              | _           -> P.parens (pp (Pexpr (t, x)))
            ) pes
        )
      | PElet (pat, pe1, pe2) ->
        !^"let" ^^^ print_pattern pat ^^^ P.equals ^^^ pp pe1
          ^^^ !^"in" ^/^ pp pe2
      | PEif (pe1, pe2, pe3) -> print_if (pp pe1) (pp pe2) (pp pe3)
      | PEis_scalar pe -> (
          match pe with
          | Pexpr (_, PEval (Vctype ty)) ->
            !^"(AilTypesAux.is_scalar(Core_aux.unproj_ctype " ^^ pp pe ^^ !^"))"
          | Pexpr (_, PEsym sym) ->
            !^"(AilTypesAux.is_scalar(Core_aux.unproj_ctype " ^^ pp pe ^^ !^"))"
          | _ -> !^"is_scalar" ^^^ pp pe
        )
      | PEis_integer pe -> (
          match pe with
          | Pexpr (_, PEval (Vctype ty)) ->
            !^"(AilTypesAux.is_integer (Core_aux.unproj_ctype "^^ pp pe ^^ !^"))"
          | Pexpr (_, PEsym sym) ->
            !^"(AilTypesAux.is_integer (Core_aux.unproj_ctype "^^ pp pe ^^ !^"))"
          | _ -> !^"is_integer" ^^^ pp pe
        )
      | PEis_signed pe -> (
          match pe with
          | Pexpr (_, PEval (Vctype ty)) ->
            !^"(AilTypesAux.is_signed_integer_type (Core_aux.unproj_ctype "
              ^^ pp pe ^^ !^"))"
          | Pexpr (_, PEsym sym) ->
            !^"(AilTypesAux.is_signed_integer_type (Core_aux.unproj_ctype "
              ^^ pp pe ^^ !^"))"
          | _ -> !^"is_signed" ^^^ pp pe
        )
      | PEis_unsigned pe -> (
          match pe with
          | Pexpr (_, PEval (Vctype ty)) ->
            !^"(AilTypesAux.is_unsigned_integer_type (Core_aux.unproj_ctype "
              ^^ pp pe ^^ !^"))"
          | Pexpr (_, PEsym sym) ->
            !^"(AilTypesAux.is_unsigned_integer_type (Core_aux.unproj_ctype "
              ^^ pp pe ^^ !^"))"
          | _ -> !^"is_unsigned" ^^^ pp pe
        )
    end
  in pp None pe

let rec print_expr = function
  | Epure pe            -> !^"A.value" ^^^ P.parens (print_pure_expr pe)
  | Ememop (memop, pes) -> todo "memop"
  | Eaction (Paction (p, (Action (_, bs, act)))) -> print_action act
  | Ecase (pe, cases) ->
    print_match (print_pure_expr pe) print_expr cases
  | Elet (pat, pe1, e2) ->
    print_let false (print_pattern pat) (print_pure_expr pe1) (print_expr e2)
  | Eif (pe1, e2, e3) ->
    print_if (print_pure_expr pe1) (print_expr e2) (print_expr e3)
  | Eskip -> !^"A.value ()"
  | Eproc (_, nm, es) ->
    print_pure_expr nm ^^^ (
      if List.length es = 0
      then P.parens P.space
      else (P.separate_map P.space (fun x -> P.parens (print_pure_expr x)) es)
    ) ^^^ !^"return"
  | Eunseq es -> raise Unsupported
  | Ewseq (pas, e1, e2) ->
    print_seq (print_pattern pas) (print_expr e1) (print_expr e2)
  | Esseq (pas, e1, e2) ->
    print_seq (print_pattern pas) (print_expr e1) (print_expr e2)
  | Easeq (None, act1, pact2) ->
      todo "aseq"
  | Easeq (Some sym, act1, pact2) ->
      todo "aseq"
  | Eindet (_, e) -> print_expr e
  | Ebound (_, e) -> print_expr e
  | End [] -> raise Unsupported
  | End (e::_) -> print_expr e
(*
  | Esave (sym, sym_tys, e) ->
    !^"let rec" ^^^ print_symbol sym ^^^ !^"return =" ^^ !> (print_expr e)
     ^/^ !^"in" ^^^ print_symbol sym ^^^ !^"return"
  | Erun (_, sym, sym_pes) -> print_symbol sym ^^^ !^"return"
*)
  | Epar _ -> raise Unsupported
  | Ewait _ -> raise Unsupported
  | Eloc (_, e) -> print_expr e

and get_ctype (Pexpr (_, pe)) =
  match pe with
  | PEval (Vctype ty) -> ty
  | _ -> print_string "ctype"; raise (Type_expected BTy_ctype)

and choose_load_type (Pexpr (_, PEval cty)) =
  match cty with
  | Vctype (Basic0 (Integer ity)) ->
    !^"A.load_integer" ^^^ P.parens (print_ail_integer_type ity)
  | Vctype (Pointer0 (q, cty)) ->
    !^"A.load_pointer" ^^^ P.parens (print_ail_qualifier q)
      ^^^ P.parens (print_ctype cty)
  | _ -> todo "load not implemented"

and choose_store_type (Pexpr (_, PEval cty)) =
  match cty with
  | Vctype (Basic0 (Integer ity)) ->
    !^"A.store_integer" ^^^ P.parens (print_ail_integer_type ity)
  | _ -> todo "store not implemented"

and print_mem_value ty e =
  match ty with
  | Basic0 (Integer ait) ->
    !^"I.MVinteger" ^^^ P.parens (print_ail_integer_type ait ^^ P.comma
                                  ^^^ print_pure_expr e)
  | Basic0 (Floating aif) -> todo "mvfloating"
  | Array0 (cty, _) -> (
    match e with
    | Pexpr(t, PEval (Vobject (OVarray cvals))) ->
      !^"I.MVarray" ^^^ print_list (print_mem_value cty)
        (List.map (fun x -> Pexpr (t, PEval (Vobject x))) cvals)
    | _ -> raise (CodegenAux.Error "Array expected")
  )
  | Pointer0 (_, cty) ->
    !^"I.MVpointer" ^^^ P.parens (print_ctype cty ^^ P.comma 
      ^^^ !^"A.pointer_from_integer_value" ^^^ P.parens (print_pure_expr e))
  | _ -> todo "print_mem_value"

and print_action act =
  match act with
  | Create (al, ty, pre) ->
    !^"A.create" ^^^ P.parens (print_symbol_prefix pre) ^^^
      P.parens (print_pure_expr al) ^^^ P.parens (print_pure_expr ty)
  | Alloc0 (al, n, pre) ->
    !^"A.alloc" ^^^ P.parens (print_symbol_prefix pre) ^^^
      P.parens (print_pure_expr al) ^^^ P.parens (print_pure_expr n)
  | Kill e ->
    !^"kill" ^^ P.parens (print_pure_expr e)
  | Store0 (ty, pe1, pe2, _) ->
    choose_store_type ty ^^^ P.parens (print_pure_expr pe1) ^^^
      P.parens (print_pure_expr pe2)
  | Load0 (ty, e, _) ->
    choose_load_type ty ^^^ P.parens (print_pure_expr e)
  | RMW0 _ -> raise Unsupported
  | Fence0 _ -> raise Unsupported

(* Print functions and function implementation specific *)
let print_params params =
  if List.length params = 0
  then P.parens P.empty
  else
    let args (sym, ty) = P.parens (print_symbol sym ^^ P.colon ^^ print_base_type ty)
    in P.separate_map P.space args params

let print_function name pmrs ty body =
  name ^^^ print_params pmrs (*^^ P.colon ^^^ ty *)^^^ P.equals ^^ !> body

let print_eff_function name pmrs ty body =
  name ^^^ print_params pmrs ^^^ !^"return" ^^^ P.equals ^^ !> body
  (*name ^^^ print_params pmrs ^^^ P.parens (!^"return" ^^ P.colon ^^ ty
    ^^ !^" -> ('a, b) Continuation") ^^^ P.equals ^^ !> body *)

let print_impls impl =
  Pmap.fold (fun iCst iDecl acc ->
    acc ^//^
    (if acc = P.empty then !^"let rec" else !^"and") ^^^
    match iDecl with
    | Def (bTy, pe) ->
      print_function (print_impl_name iCst) [] (print_base_type bTy)
        (print_pure_expr pe)
    | IFun (bTy, params, pe) ->
      print_function (print_impl_name iCst) params (print_base_type bTy)
        (print_pure_expr pe)
  ) impl P.empty

let print_funs funs =
  Pmap.fold (fun sym decl acc ->
    acc ^//^ !^"and" ^^^
    match decl with
    | Fun  (bTy, params, pe) ->
      print_function (print_symbol sym) params (print_base_type bTy)
        (print_pure_expr pe)
    | Proc (bTy, params, e) ->
      print_eff_function (print_symbol sym) params
        (P.parens (print_base_type bTy) ^^^ !^"M.memM0") (print_expr e)
  ) funs P.empty

let print_head filename =
  !^"(* Generated by Cerberus from" ^^^ !^filename ^^ !^" *)" ^//^
  !^"module A = CodegenAux" ^/^
  !^"module M = Mem" ^/^
  !^"module I = Mem.Impl" ^/^
  !^"module T = AilTypes" ^/^
  !^"module C = Core_ctype" ^/^
  !^"module O = Util.Option" ^//^
  !^"let (>>=) = Continuation.bind" ^//^
  !^"let _std_function_printf x y cont = (A.value [(I.IV (I.Prov_none, \
                            I.IVconcrete (Nat_big_num.of_string \"0\")))])" ^/^
  !^"let kill x = A.value ()"

let print_foot =
    !^"A.exit (main ())"

(* Generate Ocaml *)
let generate_ocaml core =
  let globals acc (sym, coreTy, e) =
    acc ^^ !^"and" ^^^ print_eff_function (print_symbol sym) []
      (print_base_type coreTy) (print_expr e)
  in
    print_impls core.impl ^^
    print_funs core.stdlib ^//^
    List.fold_left globals P.empty core.globs ^^
    print_funs core.funs ^^ P.semi ^^ P.semi

let compile filename core =
  let fl = Filename.chop_extension filename in
  let fl_ml = fl ^ ".ml" in
  let fl_native = fl ^ ".native" in
  let oc = open_out fl_ml in
  begin
    P.ToChannel.pretty 1. 80 oc
      (print_head filename ^^ generate_ocaml core ^//^ print_foot);
    close_out oc;
    Sys.command (
      "ocamlbuild -no-hygiene -j 4 -use-ocamlfind -pkgs pprint,zarith \
       -libs unix,nums,str " ^ fl_native (* ^ " | ./tools/colours.sh" *)
    )
    |> Exception.return0
  end
