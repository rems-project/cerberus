(* Created by Victor Gomes 2016-01-19 *)
(* It generates an Ocaml file from CPS-Core AST *)

open Util
open Pp_prelude
open Core
open Cps_core
open AilTypes
open Core_ctype

let ( ^//^ ) x y = x ^^ P.break 1 ^^ P.break 1 ^^ y
let ( !> ) x = P.nest 2 (P.break 1 ^^ x)

(* Global information of the translation unit *)
type globals = {
  interface: string;
  statics: Symbol.sym list;
  externs: Symbol.sym list;
}

let empty_globs fname = {
  interface = String.capitalize_ascii fname ^ "I.";
  statics = [];
  externs = []
}

(* String helper function *)

let string_tr target replace str =
  String.map (fun c -> if c = target then replace else c) str

(* Ocaml tokens *)

let tif    = !^"if"
let tthen  = !^"then"
let telse  = !^"else"
let tmatch = !^"match"
let twith  = !^"with"
let tlet   = !^"let"
let tletrec = !^"let rec"
let tin    = !^"in"
let tand   = !^"and"
let tfun   = !^"fun"
let tarrow = !^"->"
let tbind  = !^">>="
let tseq   = !^">>"
let tunit  = !^"()"
let tbool  = !^"bool"
let ttrue  = !^"true"
let tfalse = !^"false"
let tsome  = !^"Some"
let tnone  = !^"None"
let traise = !^"raise"
let tref   = !^"ref"

let comma_space = P.comma ^^ P.space

(* Ocaml expressions *)

let print_comment x =
  P.parens (P.star ^^^ x ^^^ P.star)

let print_let x y =
  tlet ^^^ x ^^^ P.equals ^^^ y

let print_let_in x y z =
  tlet ^^^ x ^^^ P.equals ^^^ y ^^^ tin ^/^ z

let print_let_rec d1 d2 =
  tletrec ^^^ d1 ^^^ P.equals ^^^ d2

let print_anon args =
  tfun ^^^ args ^^^ tarrow

let print_if b x y =
  tif ^^^ b ^^^ tthen ^^^ P.lparen ^^ !> x ^/^ P.rparen
            ^^^ telse ^^^ P.lparen ^^ !> y ^/^ P.rparen

let print_match m xs =
  tmatch ^^^ m ^^^ twith ^^ !>
    (List.fold_left
       (fun acc (p, x) -> P.bar ^^^ p ^^^ tarrow ^^^ x ^/^ acc)
       P.empty xs)

(* Ocaml values *)

let print_bool b = if b then ttrue else tfalse

let print_int n = !^(string_of_int n)

let print_option pp = Option.case
    (fun e -> tsome ^^^ P.parens (pp e))
    (fun _ -> tnone)

let print_pair pp (x, y) = P.parens (pp x ^^ P.comma ^^^ pp y)

let print_list pp xs = P.brackets (P.separate_map (P.semi ^^ P.space) pp xs)

let print_tuple xs = P.parens (P.separate_map comma_space id xs)

let max_int_big_num = Nat_big_num.of_int max_int

let print_num n =
  if Nat_big_num.less n max_int_big_num then
    !^"N.of_int" ^^^ print_int (Nat_big_num.to_int n)
  else
    !^"N.of_string" ^^^ P.dquotes (!^(Nat_big_num.to_string n))

let print_ref x = tref ^^^ P.parens x

(* Symbol *)

let print_symbol a = !^(Pp_symbol.to_string a)

let print_global_symbol a = !^(Pp_symbol.to_string_pretty a)

let print_raw_symbol = function
  | Symbol.Symbol (_, i, None)     ->
    !^"Symbol.Symbol" ^^^ P.parens (print_int i ^^ P.comma ^^^ tnone)
  | Symbol.Symbol (_, i, Some str) ->
    !^"RT.sym" ^^^ P.parens
      (print_int i ^^ P.comma ^^^ P.dquotes !^str)

let print_symbol_prefix = function
  | Symbol.PrefSource (_, syms) ->
    !^"Symbol.PrefSource" ^^ P.parens (!^"RT.unknown, " ^^^ print_list print_raw_symbol syms)
  | Symbol.PrefOther str   ->
    !^"Symbol.PrefOther" ^^^ P.dquotes !^str

let print_globs_prefix globs sym =
  if List.mem sym globs.statics then !^"!"
  else if List.mem sym globs.externs then !^(globs.interface)
  else P.empty

(* Take out all '.' and add '_' as prefix *)
let print_impl_name i =
  !^("_" ^ (string_tr '.' '_' (Implementation_.string_of_implementation_constant i)))

let print_cabs_id (Cabs.CabsIdentifier (loc, str)) =
  !^"RT.cabsid" ^^^ P.parens (Location_ocaml.print_location loc) ^^^ P.dquotes !^str

let print_name = function
  | Sym a  -> print_global_symbol a
  | Impl i -> print_impl_name i

(* Ail Types *)

let print_ail_integer_base_type = function
  | Ichar          -> !^"T.Ichar"
  | Short          -> !^"T.Short"
  | Int_           -> !^"T.Int_"
  | Long           -> !^"T.Long"
  | LongLong       -> !^"T.LongLong"
  | IntN_t n       -> !^"T.IntN_t" ^^^ print_int n
  | Int_leastN_t n -> !^"T.Int_leastN_t" ^^^ print_int n
  | Int_fastN_t n  -> !^"T.Int_fastN_t" ^^^ print_int n
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

let print_ail_floating_type (RealFloating ft) =
  !^"T.RealFloating" ^^^
  match ft with
  | Float ->  !^"T.Float"
  | Double -> !^"T.Double"
  | LongDouble -> !^"T.LongDouble"

let print_ail_qualifier {
  AilTypes.const = c;
  AilTypes.restrict = r;
  AilTypes.volatile = v;
  } = !^"RT.ail_qualifier" ^^^ print_tuple (List.map print_bool [c;r;v])

let print_ail_basic_type = function
  | Integer it  -> !^"T.Integer" ^^^ P.parens (print_ail_integer_type it)
  | Floating ft -> !^"T.Floating" ^^^ P.parens (print_ail_floating_type ft)

(* Patterns *)
let pp_ctor = function
  | Cnil _ ->
      "Nil"
  | Ccons ->
      "Cons"
  | Ctuple ->
      "Tuple"
  | Carray ->
      "Array"
  | Civmax ->
      "Ivmax"
  | Civmin ->
      "Ivmin"
  | Civsizeof ->
      "Ivsizeof"
  | Civalignof ->
      "Ivalignof"
  | CivCOMPL ->
      "IvCOMPL"
  | CivAND ->
      "IvAND"
  | CivOR ->
      "IvOR"
  | CivXOR ->
      "IvXOR"
  | Cspecified ->
      "Specified"
  | Cunspecified ->
      "Unspecified"
  | Cfvfromint ->
      "Cfvfromint"
  | Civfromfloat ->
      "Civfromfloat"

let rec print_pattern (Pattern (_, pat)) =
  match pat with
  | CaseBase (None, _) -> P.underscore
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (Ccons, []) -> failwith "print_patter cons"
  | CaseCtor (Ccons, [pa]) -> P.brackets @@ print_pattern pa
  | CaseCtor (Ccons, [pa1; pa2]) -> print_pattern pa1 ^^^ !^ "::" ^^^ print_pattern pa2
  | CaseCtor (ctor, pas) -> print_match_ctor (match pas with
    | []   -> P.underscore
    | [pa] -> print_pattern pa
    | _    -> P.parens (comma_list print_pattern pas)) ctor
and print_match_ctor arg = function
  | Cnil _       -> P.brackets P.empty
  | Ctuple       -> arg
  | Cspecified   -> !^"RT.Specified" ^^ P.parens arg
  | Cunspecified -> !^"RT.Unspecified" ^^ P.parens arg
  | c -> raise (Unsupported ("unsupported pattern: " ^ pp_ctor c))

let rec print_simple_pattern base (Pattern (_, pat)) =
  match pat with
  | CaseBase (None, _) -> base
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (_, pas) ->
    begin match pas with
    | []   -> P.parens P.empty
    | [pa] -> print_simple_pattern base pa
    | _    -> P.parens (comma_list (print_simple_pattern base) pas)
    end

let print_call_pattern = print_simple_pattern (P.parens P.empty)

let print_fun_pattern = print_simple_pattern P.underscore

let print_case pe pp pas =
  let cmp (pat1, pe1) (pat2, pe2) =
    match pat1, pat2 with
    | _, Pattern (_, CaseBase (None, _)) -> 1
    | _ -> 0
  in
  (* ensure that the pattern "_" is the first in the list,
     it will be the last by fold_left *)
  let pas = List.fast_sort cmp pas in
  print_match pe (List.map (fun (p, e) -> (print_pattern p, pp e)) pas)

(* Core ctypes *)

let rec print_ctype = function
  | Void0 ->
    !^"C.Void0"
  | Basic0 (Integer Char) ->
    !^"RT.char_t"
  | Basic0 (Integer Bool) ->
    !^"RT.bool_t"
  | Basic0 (Integer (Signed Ichar)) ->
    !^"RT.schar_t"
  | Basic0 (Integer (Unsigned Ichar)) ->
    !^"RT.uchar_t"
  | Basic0 (Integer (Signed Short)) ->
    !^"RT.short_t"
  | Basic0 (Integer (Unsigned Short)) ->
    !^"RT.ushort_t"
  | Basic0 (Integer (Signed Long)) ->
    !^"RT.long_t"
  | Basic0 (Integer (Unsigned Long)) ->
    !^"RT.ulong_t"
  | Basic0 (Integer (Signed LongLong)) ->
    !^"RT.longlong_t"
  | Basic0 (Integer (Unsigned LongLong)) ->
    !^"RT.ulonglong_t"
  | Basic0 (Integer (Signed Int_)) ->
    !^"RT.int_t"
  | Basic0 (Integer (Unsigned Int_)) ->
    !^"RT.uint_t"
  | Basic0 (Integer Size_t) ->
    !^"RT.size_t"
  | Basic0 (Integer Ptrdiff_t) ->
    !^"RT.ptrdiff_t"
  | Basic0 (Floating (RealFloating Float)) ->
    !^"RT.float_t"
  | Basic0 (Floating (RealFloating Double)) ->
    !^"RT.double_t"
  | Basic0 (Floating (RealFloating LongDouble)) ->
    !^"RT.longdouble_t"
  | Basic0 abt ->
    !^"C.Basic0" ^^^ P.parens (print_ail_basic_type abt)
  | Array0 (cty, num) ->
    !^"C.Array0" ^^^ P.parens (print_ctype cty ^^ P.comma
                               ^^^ print_option print_num num)
  | Function0 ((q, cty), params, variad) ->
    !^"C.Function0" ^^^ P.parens
      (P.parens (print_ail_qualifier q ^^ P.comma ^^^ print_ctype cty) ^^ P.comma
       ^^^ print_list (fun (q, cty) -> print_ail_qualifier q ^^ P.comma
                                       ^^^ print_ctype cty) params
       ^^ P.comma ^^^ print_bool variad)
  | Pointer0 (q, cty) ->
    !^"C.Pointer0" ^^^ P.parens (print_ail_qualifier q ^^ P.comma
                                 ^^^ print_ctype cty)
  | Atomic0 cty ->
    !^"C.Atomic0" ^^^ P.parens (print_ctype cty)
  | Struct0 strct ->
    !^"C.Struct0" ^^^ P.parens (print_raw_symbol strct)
  | Union0 union ->
    !^"C.Union0" ^^^ P.parens (print_raw_symbol union)
  | Builtin0 str ->
    !^"C.Builtin0" ^^^ !^str

(* Memory types *)

let print_integer_value iv =
  Ocaml_mem.case_integer_value iv
    (fun n -> !^"RT.mk_int" ^^^ P.dquotes (!^(Nat_big_num.to_string n)))
    (fun _ -> raise (Unexpected "iv value"))

let print_float_value fv =
  Ocaml_mem.case_fval fv
    (fun _ -> raise (Unexpected "fv value"))
    (fun x -> !^"RT.mk_float" ^^^ P.dquotes (!^(string_of_float x)))

let print_pointer_value pv =
  Ocaml_mem.case_ptrval pv
    (fun _ -> !^"RT.mk_null_void")
    (fun _ -> failwith "ERROR")
    (fun opt_i addr -> !^"RT.mk_pointer"
                       ^^^ print_option (fun n -> P.dquotes (!^(Nat_big_num.to_string n))) opt_i
                       ^^^ P.dquotes (!^(Nat_big_num.to_string addr)))
    (fun _ -> raise (Unexpected "ptr value"))

(* Core Types *)

(* THIS IS ONLY USED WHEN TYPE ANNOTATING *)
let rec print_core_object = function
  | OTy_integer    -> !^"M.integer_value"
  | OTy_floating   -> !^"M.floating_value"
  | OTy_pointer    -> !^"M.pointer_value"
  (*| OTy_cfunction (ret_oTy, naparams, isVariadic) ->
     (* TODO: K wip *)
     !^"M.pointer_value" (* cfunction is a pointer value? *)
                       (*TODO: I am not sure about these: *) *)
  | OTy_array obj  -> !^"[" ^^ print_core_object obj ^^ !^"]"
  | OTy_struct sym -> !^"struct" ^^^ print_symbol sym
  | OTy_union sym  -> !^"union" ^^^ print_symbol sym

let rec print_base_type = function
  | BTy_unit       -> tunit
  | BTy_boolean    -> tbool
  | BTy_ctype      -> !^"C.ctype0"
  | BTy_list bTys  -> P.parens (print_base_type bTys) ^^^ !^"list"
  | BTy_tuple bTys -> P.parens (P.separate_map P.star print_base_type bTys)
  | BTy_object obj -> print_core_object obj
  | BTy_loaded obj -> P.parens (print_core_object obj) ^^^ !^"RT.loaded"
  | BTy_storable   -> assert false

let print_core_type = function
  | TyBase   baseTy -> print_base_type baseTy
  | TyEffect baseTy -> print_base_type baseTy

(* print functions and function implementation specific *)

let print_params params =
  if List.length params = 0 then
    P.parens P.empty
  else
    let args (sym, ty) =
      P.parens (print_symbol sym (*^^ P.colon ^^ print_base_type ty*))
    in P.separate_map P.space args params

let print_function name pmrs ty body =
  name ^^^ print_params pmrs (*^^ P.colon ^^^ ty *)^^^ P.equals ^^ !> body

let print_eff_function name pmrs ty body =
  name ^^^ print_params pmrs ^^^ P.equals ^^ !> body

(* Binary operations and precedences *)

let print_binop bop pp (Pexpr (_, t1, pe1_) as pe1) (Pexpr (_, t2, pe2_) as pe2) =
  let app bop = !^bop ^^^ P.parens (pp pe1) ^^^ P.parens (pp pe2) in
  let unexpected ty () =
    raise (Unexpected ("Unexpected binary operator for " ^ ty))
  in
  let case_by_type intop floatop ptrop ctyop =
    match t1 with
    | BTy_object (OTy_integer)
    | BTy_loaded (OTy_integer) ->
      app intop
    | BTy_object (OTy_floating)
    | BTy_loaded (OTy_floating) ->
      Option.case app (unexpected "floats") floatop
    | BTy_object (OTy_pointer)
    | BTy_loaded (OTy_pointer) ->
      Option.case app (unexpected "pointers") ptrop
    | BTy_ctype ->
      Option.case app (unexpected "ctypes") ctyop
    | _ -> raise (Unexpected "Unknown binary operator")
  in
  match bop with
  | OpAdd -> case_by_type "RT.add" (Some "RT.addf") None None
  | OpSub -> case_by_type "RT.sub" (Some "RT.subf") None None
  | OpMul -> case_by_type "RT.mul" (Some "RT.mulf") None None
  | OpDiv -> case_by_type "RT.div" (Some "RT.divf") None None
  | OpRem_t -> case_by_type "RT.remt" None None None
  | OpRem_f -> case_by_type "RT.remf" None None None
  | OpExp -> case_by_type "RT.exp" None None None
  | OpEq  -> case_by_type "RT.eq" (Some "M.eq_fval") (Some "M.eq_ptrval") (Some "C.ctypeEqual0")
  | OpLt  -> case_by_type "RT.lt" (Some "M.lt_fval") (Some "M.lt_ptrval") None
  | OpLe  -> case_by_type "RT.le" (Some "M.le_fval") (Some "M.le_ptrval") None
  | OpGt  -> case_by_type "RT.gt" (Some "M.gt_fval") (Some "M.gt_ptrval") None
  | OpGe  -> case_by_type "RT.ge" (Some "M.ge_fval") (Some "M.ge_ptrval") None
  | OpAnd -> pp pe1 ^^^ !^" && " ^^^ pp pe2
  | OpOr  -> pp pe1 ^^^ !^ "||" ^^^ pp pe2

let binop_precedence (Pexpr (_, _, pe)) = match pe with
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

let rec print_object_value globs = function
  | OVstruct _
  | OVunion  _          -> failwith "TODO: NOT SURE IF THIS CAN HAPPEN!"
  (*| OVcfunction (Sym s) -> print_globs_prefix globs s ^^ print_global_symbol s
  | OVcfunction nm      -> print_name nm *)
  | OVinteger iv        -> print_integer_value iv
  | OVfloating fv       -> print_float_value fv
  | OVpointer pv        -> print_pointer_value pv
  | OVarray lvs         -> print_list (print_loaded_value globs) lvs

and print_loaded_value globs = function
  | LVspecified v ->
    !^"RT.Specified" ^^^ P.parens (print_object_value globs v)
  | LVunspecified ty ->
    !^"RT.Unspecified" ^^^ P.parens (print_ctype ty)

let rec print_value globs = function
  | Vunit        -> tunit
  | Vtrue        -> ttrue
  | Vfalse       -> tfalse
  | Vlist _      -> failwith "TODO: this need to be lifted to memvalues, otherwise it does not type check!"
  | Vtuple cvals -> failwith "TODO: this need to be lifted to memvalues, otherwise it does not type check!"
  | Vctype ty    -> print_ctype ty
  | Vobject obv  -> print_object_value globs obv
  | Vloaded lv   -> print_loaded_value globs lv

let print_is_expr str pp pe =
  match pe with
  | Pexpr (_, _, PEval (Vctype _))
  | Pexpr (_, _, PEsym _) -> !^"RT." ^^ !^str ^^^ P.parens (pp pe)
  | _ -> !^str ^^^ pp pe

let print_basic_mval_conv = function
  | Integer it  -> !^"RT.conv_int_mval" ^^^ P.parens (print_ail_integer_type it)
  | Floating ft ->  !^"RT.conv_float_mval" ^^^ P.parens (print_ail_floating_type ft)

let print_mval_conv = function
  | Void0 ->
    failwith "choose_mval_conv: void is not a memory value"
  | Basic0 abt ->
    print_basic_mval_conv abt
  | Array0 (cty, num) ->
    failwith "TODO: print_mval_conv: array"
  | Function0 ((q, cty), params, variad) ->
    failwith "TODO: print_mval_conv: function"
  | Pointer0 (q, cty) ->
    !^"RT.conv_ptr_mval" ^^^ P.parens (print_ctype cty)
  | Atomic0 cty ->
    failwith "TODO: print_mval_conv: atomic"
  | Struct0 struct_tag ->
    !^"RT.conv_struct_mval" ^^^ P.parens (print_raw_symbol struct_tag)
  | Union0 union_tag ->
    failwith "TODO: print_mval_conv: union"
  | Builtin0 str ->
    failwith "TODO: print_mval_conv: builtin"


(* WARN: The list needs to be converted to memory values, otherwise it cannot typecheck in Ocaml *)
let print_tag pp tags (cid, pe) =
  match List.assq_opt cid tags with
  | Some cty -> P.parens (print_cabs_id cid ^^ P.comma ^^^ print_mval_conv cty ^^^ P.parens (pp pe))
  | None -> raise (Unexpected "Identifier doesn't exist in the tags list")

let get_tags s =
  match Pmap.lookup s (Tags.tagDefs ()) with
  | Some (Tags.StructDef tags)
  | Some (Tags.UnionDef tags) -> tags
  | None -> raise (Unexpected "Identifier not found in tags")

let print_tags pp s vals =
  let tags = get_tags s in
  print_list (print_tag pp tags) vals

let print_ctor pp ctor pes =
  let pp_args sep = P.parens (P.separate_map sep (fun x -> P.parens (pp x)) pes) in
  let pp_array () = P.brackets (P.separate_map P.semi (fun x -> P.parens (pp x)) pes) in
  match ctor with
  | Cnil _ -> !^"[]"
  | Ccons ->
    (match pes with
     | []       -> raise (Unexpected "Ccons: empty list")
     | [pe]     -> P.brackets (pp pe)
     | [pe;pes] -> pp pe ^^^ !^"::" ^^^ pp pes
     | _        -> raise (Unexpected "Ccons: more than 2 args")
    )
  | Ctuple       -> pp_args P.comma
  | Carray       -> (*!^"RT.mk_array" ^^^*) pp_array ()
  | Civmax       -> !^"RT.ivmax" ^^^ pp_args P.space
  | Civmin       -> !^"RT.ivmin" ^^^ pp_args P.space
  | Civsizeof    -> !^"M.sizeof_ival" ^^^ pp_args P.space
  | Civalignof   -> !^"M.alignof_ival" ^^^ pp_args P.space
  | Cspecified   -> !^"RT.Specified" ^^^ pp_args P.space
  | Cunspecified -> !^"RT.Unspecified" ^^^ pp_args P.space
  | CivCOMPL     -> !^"RT.ivcompl" ^^^ pp_args P.space
  | CivAND       -> !^"RT.ivand" ^^^ pp_args P.space
  | CivOR        -> !^"RT.ivor" ^^^ pp_args P.space
  | CivXOR       -> !^"RT.ivxor" ^^^ pp_args P.space
  | Cfvfromint   -> !^"RT.fvfromint" ^^^ pp_args P.space
  | Civfromfloat -> !^"RT.ivfromfloat" ^^^ pp_args P.comma


let print_pure_expr globs pe =
  let rec pp prec pe =
    let prec' = binop_precedence pe in
    let pp z  = P.group (pp prec' z) in
    (if lt_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with Pexpr (_, t, pe') ->
      match pe' with
      | PEsym sym ->
        print_globs_prefix globs sym ^^ print_symbol sym
      | PEimpl iCst -> print_impl_name iCst ^^^ P.parens P.space
      | PEval cval -> print_value globs cval
      | PEconstrained _ -> raise (Unexpected "Unexpected contrained expression.")
      | PEundef (_, ub) ->
        traise ^^^ P.parens (!^"RT.Undefined" ^^^ P.dquotes
                               (!^(Undefined.stringFromUndefined_behaviour ub)))
      | PEerror (str, pe) ->
        traise ^^^ P.parens (!^"RT.Error" ^^^ P.dquotes (!^str ^^^ pp pe))
      | PEctor (ctor, pes) -> print_ctor pp ctor pes
      | PEcase (pe, pas) -> P.parens (print_case (pp pe) pp pas)
      | PEarray_shift (pe1, ty, pe2) ->
        !^"M.array_shift_ptrval" ^^^ P.parens (pp pe1)
        ^^^ P.parens (print_ctype ty) ^^^ P.parens (pp pe2)
      | PEmember_shift (pe, sym, id) ->
        !^"M.member_shift_ptrval" ^^^ P.parens (pp pe)
        ^^^ P.parens (print_raw_symbol sym) ^^^ P.parens (print_cabs_id id)
      | PEnot pe -> !^"not" ^^^ P.parens (pp pe)
      | PEop (bop, pe1, pe2) -> print_binop bop pp pe1 pe2
        (* struct/union are serialised as tuples *)
      | PEstruct (s, tags) ->
        print_tags pp s tags
      | PEmemberof (s, cid, pe) ->
        failwith "TODO: PEmemberof"
      | PEunion (s, cid, pe) ->
        P.parens (print_raw_symbol s) (*TODO: (* ^^^ print_tag pp (cid, pe))*)*)
      | PEcall (nm, pes) ->
        print_name nm ^^^ (
          if List.length pes = 0
          then P.parens P.empty
          else P.separate_map P.space (fun (Pexpr (_, t, x)) ->
              match x with
              | (PEsym sym) -> pp (Pexpr ([], t, PEsym sym))
              | _           -> P.parens (pp (Pexpr ([], t, x)))
            ) pes
        )
      | PElet (p, pe1, pe2) -> print_let_in (print_pattern p) (pp pe1) (pp pe2)
      | PEif (pe1, pe2, pe3) -> print_if (pp pe1) (pp pe2) (pp pe3)
      | PEis_scalar pe -> print_is_expr "is_scalar" pp pe
      | PEis_integer pe -> print_is_expr "is_scalar" pp pe
      | PEis_signed pe -> print_is_expr "is_signed" pp pe
      | PEis_unsigned pe -> print_is_expr "is_unsigned" pp pe
      | PEcfunction _
      | PEare_compatible _ -> assert false
    end
  in pp None pe

let print_memop globs memop pes =
  (match memop with
   | Mem_common.PtrEq -> !^"M.eq_ptrval"
   | Mem_common.PtrNe -> !^"M.ne_ptrval"
   | Mem_common.PtrGe -> !^"M.ge_ptrval"
   | Mem_common.PtrLt -> !^"M.lt_ptrval"
   | Mem_common.PtrGt -> !^"M.gt_ptrval"
   | Mem_common.PtrLe -> !^"M.le_ptrval"
   | Mem_common.Ptrdiff -> !^"M.diff_ptrval"
   | Mem_common.IntFromPtr -> !^"RT.intcast_ptrval"
   | Mem_common.PtrFromInt -> !^"M.ptrcast_ival"
   | Mem_common.PtrValidForDeref -> !^"RT.valid_for_deref_ptrval"
   | Mem_common.Memcmp -> !^"RT.memcmp"
   | Mem_common.Memcpy -> !^"RT.memcpy"
   | Mem_common.Realloc -> !^"RT.realloc"
   | Mem_common.PtrWellAligned -> !^"RT.ptr_well_aligned"
   | Mem_common.PtrArrayShift -> failwith "TODO: print_memop: PtrArrayShift"
  ) ^^^ (P.separate_map P.space (P.parens % print_pure_expr globs)) pes

let choose_load_type pe =
  let get_ctype = function
    | Pexpr (_, _, PEval (Vctype cty)) -> cty
    | pe -> failwith @@ "fatal error: get_type: " ^ String_core.string_of_pexpr pe
  in
  match get_ctype pe with
  | Void0 ->
    raise (Unexpected "cannot load a void type")
  | Basic0 (Integer ity) ->
    !^"RT.load_integer" ^^^ P.parens (print_ail_integer_type ity)
  | Basic0 (Floating fty) ->
    !^"RT.load_float" ^^^ P.parens (print_ail_floating_type fty)
  | Pointer0 (q, cty) ->
    !^"RT.load_pointer" ^^^ P.parens (print_ail_qualifier q)
      ^^^ P.parens (print_ctype cty)
  | Array0 (cty, n) ->
    !^"RT.load_array"
      ^^^ P.parens (print_ctype cty)
      ^^^ P.parens (print_option print_num n)
  | Function0 _ ->
    raise (Unexpected "cannot load a function type")
  | Struct0 s ->
    !^"RT.load_struct" ^^^ P.parens (print_raw_symbol s)
  | Union0 s ->
    !^"RT.load_union" ^^^ P.parens (print_raw_symbol s)
  | Atomic0 _ ->
    raise (Unsupported "load atomic is not implemented")
  | Builtin0 _ ->
    raise (Unsupported "load builtin is not implemented")

(* TODO: check this array type storage *)
let print_store_array_type = function
  | Basic0 (Integer ity) ->
    !^"RT.store_array_of_int" ^^^ P.parens (print_ail_integer_type ity)
  | Basic0 (Floating fty) ->
    !^"RT.store_array_of_float" ^^^ P.parens (print_ail_floating_type fty)
  | Pointer0 (q, cty) ->
    !^"RT.store_array_of_ptr" ^^^ P.parens (print_ail_qualifier q)
      ^^^ P.parens (print_ctype cty)
  | Struct0 s ->
    !^"RT.store_array_of_struct" ^^^ P.parens (print_raw_symbol s)
  | _ -> raise (Unsupported "store array not implemented")

let choose_store_type pe =
  let get_ctype = function
    | Pexpr (_, _, PEval (Vctype cty)) -> cty
    | Pexpr (_, _, PEsym (Symbol.Symbol (_, _, Some n))) -> (Basic0 (Integer AilTypes.Char)) (* failwith ("choose_store: PEsym: " ^ n) *)
    | pe -> failwith @@ "fatal error: get_type: " ^ String_core.string_of_pexpr pe
  in
  match get_ctype pe with
  | Basic0 (Integer ity) ->
    !^"RT.store_integer" ^^^ P.parens (print_ail_integer_type ity)
  | Pointer0 (q, cty) ->
    !^"RT.store_pointer" ^^^ P.parens (print_ail_qualifier q)
      ^^^ P.parens (print_ctype cty)
  | Struct0 s ->
    !^"RT.store_struct" ^^^ P.parens (print_raw_symbol s)
  | Union0 s ->
    !^"RT.store_union" ^^^ P.parens (print_raw_symbol s)
  | Array0 (cty, n) ->
    print_store_array_type cty
      ^^^ P.parens (print_option print_num n)
  | _ -> raise (Unsupported "store not implemented")

let print_action globs act =
  match act with
  | Create (al, ty, pre) ->
    !^"RT.create"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs ty)
    ^^^ tnone
  | CreateReadOnly (al, ty, x, pre) ->
    !^"RT.create"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs ty)
    ^^^ P.parens (tsome ^^ P.parens (print_pure_expr globs x))
  | Alloc0 (al, n, pre) ->
    !^"RT.alloc"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs n)
  | Kill (b, e) ->
    !^"M.kill" ^^^ !^"RT.unknown" ^^^ print_bool b ^^^ P.parens (print_pure_expr globs e)
  | Store0 (b, ty, pe1, pe2, _) ->
    choose_store_type ty
    ^^^ print_bool b
    ^^^ P.parens (print_pure_expr globs pe1)
    ^^^ P.parens (print_pure_expr globs pe2)
  | Load0 (ty, e, _) ->
    choose_load_type ty ^^^ P.parens (print_pure_expr globs e)
  | RMW0 _ -> raise (Unsupported "Operation RMW is currently not supported.")
  | Fence0 _ -> raise (Unsupported "Operation Fence is currenly not supported.")

(* Implementation constants *)

let print_impls globs impl =
  Pmap.fold (fun iCst iDecl acc ->
      acc ^//^ tand ^^^
    match iDecl with
    | Def (bTy, pe) ->
      print_function (print_impl_name iCst)
        []
        (print_base_type bTy)
        (print_pure_expr globs pe)
    | IFun (bTy, params, pe) ->
      print_function
        (print_impl_name iCst)
        params
        (print_base_type bTy)
        (print_pure_expr globs pe)
  ) impl P.empty

(* CPS core *)

let rec print_basic_expr globs = function
  | CpsPure pe            -> !^"RT.return" ^^^ P.parens (print_pure_expr globs pe)
  | CpsMemop (memop, pes) -> print_memop globs memop pes
  | CpsAction (Core.Paction (p, (Action (_, bs, act)))) -> print_action globs act

let print_call globs (sym, pes, pato) =
  P.parens (print_symbol sym (*^^  !^"[@tailcall]"*))
  ^^^ P.parens (P.separate_map comma_space (print_pure_expr globs) pes)
  ^^^ P.parens (Option.case print_call_pattern (fun _ -> P.empty) pato)

let rec print_control globs = function
  | CpsGoto goto -> print_call globs goto
  | CpsIf (pe1, goto2, goto3) ->
    print_if (print_pure_expr globs pe1)
      (print_control globs goto2)
      (print_control globs goto3)
  | CpsCase (pe, cases) ->
    P.parens (print_case (print_pure_expr globs pe) (print_control globs) cases)
  | CpsProc (nm, (l, fvs), pes) ->
    print_name nm
    ^^^ P.parens (print_symbol l
                  ^^^ P.parens (P.separate_map comma_space print_symbol fvs))
    ^^^ P.separate_map P.space (fun x -> P.parens (print_pure_expr globs x)) pes

  | CpsCcall (nm, (l, fvs), es) ->
    print_pure_expr globs nm ^^^
    P.parens (print_symbol l
              ^^^ P.parens (P.separate_map comma_space print_symbol fvs))
    ^^^ (
      if List.length es = 0 then tunit
      else P.separate_map P.space (fun x -> P.parens (print_pure_expr globs x)) es
    )
  | CpsCont sym ->
    !^"cont_0" ^^^ print_symbol sym
  | CpsNd ces ->
    !^"RT.nd"
    ^^^ print_int (List.length ces)
    ^^^ print_list (print_control globs) ces

let print_seq = function
  | Some (Pattern (_, CaseBase (None, _)))
  | Some (Pattern (_, CaseCtor (_, [])))
  | None -> tbind ^^^ tfun ^^^ P.underscore ^^^ tarrow ^^ P.break 1
  | Some p -> tbind ^^^ print_anon (print_pattern p) ^^ P.break 1

let print_bb globs (es, (pato, ct)) =
  match es with
  | [] -> print_control globs ct
  | ((_, e)::es) ->
    print_basic_expr globs e
    ^^ List.fold_left
      (fun acc (p, e) -> acc ^/^ print_seq p ^^ print_basic_expr globs e)
      P.space es
    ^/^ print_seq pato ^^ print_control globs ct

let print_decl globs (BB ((sym, pes, pato), bb)) =
  print_symbol sym
  ^^^ P.parens (P.separate_map comma_space print_symbol pes)
  ^^^ Option.case print_fun_pattern (fun _ -> P.underscore) pato
  ^^^ P.equals ^^ !> (print_bb globs bb)

let print_transformed globs bbs bb =
  let bbs = List.sort_uniq block_compare bbs in
  if List.length bbs = 0 then
    print_bb globs bb
  else
    tletrec
    ^^^ print_decl globs (List.hd bbs)
    ^^^ List.fold_left
      (fun acc decl -> acc ^/^ tand ^^^ print_decl globs decl)
      P.space (List.tl bbs)
    ^/^ tin ^/^ print_bb globs bb

let print_funs globs ?init:(flag=true) funs =
  Pmap.fold (fun sym decl acc ->
      (if acc = P.empty && flag then tletrec else acc ^//^ tand) ^^^
      match decl with
      | CpsFun  (bTy, params, pe) ->
        print_function
          (print_global_symbol sym)
          params
          (print_base_type bTy)
          (print_pure_expr globs pe)
      | CpsProc (bTy, params, bbs, bbody) ->
        print_eff_function
          (print_global_symbol sym ^^^ print_symbol default)
          params
          (P.parens (print_base_type bTy) ^^^ !^"M.memM")
          (print_transformed globs bbs bbody)
    ) funs P.empty
