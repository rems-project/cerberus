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
    !^"B.of_int" ^^^ print_int (Nat_big_num.to_int n)
  else
    !^"B.of_string" ^^^ P.dquotes (!^(Nat_big_num.to_string n))

let print_ref x = tref ^^^ P.parens x

(* Symbol *)

let print_symbol a = !^(Pp_symbol.to_string a)

let print_global_symbol a = !^(Pp_symbol.to_string_pretty a)

let print_raw_symbol = function
  | Symbol.Symbol (i, None)     ->
    !^"Symbol.Symbol" ^^^ P.parens (print_int i ^^ P.comma ^^^ tnone)
  | Symbol.Symbol (i, Some str) ->
    !^"Symbol.Symbol" ^^^ P.parens
      (print_int i ^^ P.comma ^^^ tsome ^^^ P.dquotes !^str)

let print_symbol_prefix = function
  | Symbol.PrefSource syms ->
    !^"Symbol.PrefSource" ^^^ print_list print_raw_symbol syms
  | Symbol.PrefOther str   ->
    !^"Symbol.PrefOther" ^^^ P.dquotes !^str

let print_globs_prefix globs sym =
  if List.mem sym globs.statics then !^"!"
  else if List.mem sym globs.externs then !^(globs.interface)
  else P.empty

(* Take out all '.' and add '_' as prefix *)
let print_impl_name i =
  !^("_" ^ (string_tr '.' '_' (Implementation_.string_of_implementation_constant i)))
let print_loc loc =
  let print_lex pos =
    !^"A.position" ^^^ P.dquotes !^(pos.Lexing.pos_fname)
    ^^^ !^(string_of_int pos.Lexing.pos_lnum)
    ^^^ !^(string_of_int pos.Lexing.pos_bol)
    ^^^ !^(string_of_int pos.Lexing.pos_cnum)
  in
  let open Location_ocaml in
  match loc with
  | Loc_unknown ->
    !^"Location_ocaml.unknown"
  | Loc_other str ->
      !^ "Location_ocaml.other" ^^ P.parens (P.dquotes !^ (String.escaped str))
  | Loc_point pos ->
    !^"Location_ocaml.point" ^^^ P.parens (print_lex pos)
  | Loc_region (pos1, pos2, opos3) ->
    !^"Location_ocaml.Loc_region"
      ^^^ P.parens (print_lex pos1)
      ^^^ P.parens (print_lex pos2)
      ^^^ P.parens (print_option print_lex opos3)

let print_cabs_id (Cabs.CabsIdentifier (loc, str)) =
  !^"Cabs.CabsIdentifier" ^^^ P.parens(print_loc loc ^^ P.comma ^^^ P.dquotes !^str)

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

let print_ail_qualifier {
  AilTypes.const = c;
  AilTypes.restrict = r;
  AilTypes.volatile = v;
(*  AilTypes.atomic = a; *)
  } = !^"A.ail_qualifier" ^^^ print_tuple (List.map print_bool [c;r;v(*;a*)])

let print_ail_basic_type = function
  | Integer it  -> !^"T.Integer" ^^^ P.parens (print_ail_integer_type it)
  | Floating (RealFloating ft) ->
    let print_floating_type = function
      | Float -> !^"Float"
      | Double -> !^"Double"
      | LongDouble -> !^"LongDouble"
    in !^"Floating" ^^^ P.parens (!^"RealFloating" ^^^ print_floating_type ft)

(* Patterns *)

let rec print_pattern = function
  | CaseBase (None, _) -> P.underscore
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (ctor, pas) -> print_match_ctor (match pas with
    | []   -> P.underscore
    | [pa] -> print_pattern pa
    | _    -> P.parens (comma_list print_pattern pas)) ctor
and print_match_ctor arg = function
  | Cnil _       -> P.brackets P.empty
  | Ccons        -> !^"Cons"
  | Ctuple       -> arg
  | Carray       -> !^"A.array" ^^ P.parens arg
  | Civmax       -> !^"A.ivmax"
  | Civmin       -> !^"A.ivmin"
  | Civsizeof    -> !^"M.sizeof_ival"
  | Civalignof   -> !^"M.alignof_ival"
  | Cspecified   -> !^"A.Specified" ^^ P.parens arg
  | Cunspecified -> !^"A.Unspecified" ^^ P.parens arg
  | CivCOMPL     -> !^"A.ivcompl"
  | CivAND       -> !^"A.ivand"
  | CivOR        -> !^"A.ivor"
  | CivXOR       -> !^"A.ivxor"
  | Cfvfromint   -> !^"A.fvfromint"
  | Civfromfloat -> !^"A.ivfromfloat"

let rec print_call_pattern = function
  | CaseBase (None, _) -> P.parens P.empty (* WARNING: should this ever match? *)
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (_, pas) ->
    begin match pas with
    | []   -> P.parens P.empty
    | [pa] -> print_call_pattern pa
    | _    -> P.parens (comma_list print_call_pattern pas)
    end

let rec print_fun_pattern = function
  | CaseBase (None, _) -> P.underscore
  | CaseBase (Some sym, _) -> print_symbol sym
  | CaseCtor (_, pas) ->
    begin match pas with
    | []   -> P.parens P.empty
    | [pa] -> print_fun_pattern pa
    | _    -> P.parens (comma_list print_fun_pattern pas)
    end

let print_case pe pp pas =
  let cmp (pat1, pe1) (pat2, pe2) =
    match pat1, pat2 with
    | _, CaseBase (None, _) -> 1
    | _ -> 0
  in
  (* ensure that the pattern "_" is the first in the list,
     it will be the last by fold_left *)
  let pas = List.fast_sort cmp pas in
  print_match pe (List.map (fun (p, e) -> (print_pattern p, pp e)) pas)

(* Core ctypes *)

let rec print_ctype = function
  | Void0 -> !^"C.Void0"
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
  | Atomic0 cty -> !^"C.Atomic0" ^^^ P.parens (print_ctype cty)
  | Struct0 strct -> !^"C.Struct0" ^^^ P.parens (print_raw_symbol strct)
  | Union0 union -> !^"C.Union0" ^^^ P.parens (print_raw_symbol union)
  | Builtin0 str -> !^"C.Builtin0" ^^^ !^str

(* Memory types *)

let print_integer_value iv =
  Ocaml_mem.case_integer_value iv
    (fun n -> !^"A.mk_int" ^^^ P.dquotes (!^(Nat_big_num.to_string n)))
    (fun _ -> raise (Unexpected "iv value"))

let print_float_value fv =
  Ocaml_mem.case_fval fv
    (fun _ -> raise (Unexpected "fv value"))
    (fun x -> !^"A.mk_float" ^^^ P.dquotes (!^(string_of_float x)))

let print_pointer_value pv =
  Ocaml_mem.case_ptrval pv
    (fun _ -> !^"A.mk_null_void")
    (fun opt_i addr -> !^"A.mk_pointer"
                       ^^^ print_option (fun n -> P.dquotes (!^(Nat_big_num.to_string n))) opt_i
                       ^^^ P.dquotes (!^(Nat_big_num.to_string addr)))
    (fun _ -> raise (Unexpected "ptr value"))

(* Core Types *)

(* THIS IS ONLY USED WHEN TYPE ANNOTATING *)
let rec print_core_object = function
  | OTy_integer    -> !^"M.integer_value"
  | OTy_floating   -> !^"M.floating_value"
  | OTy_pointer    -> !^"M.pointer_value"
  | OTy_cfunction (ret_oTy, naparams, isVariadic) ->
     (* TODO: K wip *)
     !^"M.pointer_value" (* cfunction is a pointer value? *)
                       (*TODO: I am not sure about these: *)
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
  | BTy_loaded obj -> P.parens (print_core_object obj) ^^^ !^"A.loaded"

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
  let case_by_type f g h =
    match t1 with
    | BTy_object (OTy_integer)
    | BTy_loaded (OTy_integer) -> app f
    | BTy_object (OTy_pointer)
    | BTy_loaded (OTy_pointer) -> app g
    | BTy_ctype -> begin match h with
        | Some h -> app h
        | None -> raise (Unexpected "Unexpected binary operator for ctypes")
      end
    | _ -> raise (Unexpected "Unknown binary operator")
  in
  match bop with
  | OpAdd -> app "A.add"
  | OpSub -> app "A.sub"
  | OpMul -> app "A.mul"
  | OpDiv -> app "A.div"
  | OpRem_t -> app "A.remt"
  | OpRem_f -> app "A.remf"
  | OpExp -> app "A.exp"
  | OpEq  -> case_by_type "A.eq" "A.eq_ptrval" (Some "C.ctypeEqual0")
  | OpLt  -> case_by_type "A.lt" "A.lt_ptrval" None
  | OpLe  -> case_by_type "A.le" "A.le_ptrval" None
  | OpGt  -> case_by_type "A.gt" "A.gt_ptrval" None
  | OpGe  -> case_by_type "A.ge" "A.ge_ptrval" None
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
  | OVunion  _          -> raise (Unsupported "struct or union")
  | OVcfunction (Sym s) -> print_globs_prefix globs s ^^ print_global_symbol s
  | OVcfunction nm      -> print_name nm
  | OVinteger iv        -> print_integer_value iv
  | OVfloating fv       -> print_float_value fv
  | OVpointer pv        -> print_pointer_value pv
  | OVarray lvs         -> print_list (print_loaded_value globs) lvs
  | OVcomposite _       -> raise (Unsupported "OVcomposite")

and print_loaded_value globs = function
  | LVspecified v ->
      !^"A.Specified" ^^^ P.parens (print_object_value globs v)
  | LVunspecified ty ->
      !^"A.Unspecified" ^^^ P.parens (print_ctype ty)

let rec print_value globs = function
  | Vunit            -> tunit
  | Vtrue            -> ttrue
  | Vfalse           -> tfalse
  | Vlist (_, cvals) -> print_list (print_value globs) cvals
  | Vtuple cvals     -> P.parens (comma_list (print_value globs) cvals)
  | Vctype ty        -> print_ctype ty
  | Vobject obv      -> print_object_value globs obv
  | Vloaded lv       -> print_loaded_value globs lv
(*  | Vconstrained _   -> raise (Unsupported "Unsupported constrained values.") *)

let print_is_expr str pp pe =
  match pe with
  | Pexpr (_, _, PEval (Vctype _))
  | Pexpr (_, _, PEsym _) -> !^"A." ^^ !^str ^^^ P.parens (pp pe)
  | _ -> !^str ^^^ pp pe

let print_tag pp (cid, pe) =
  P.parens (print_cabs_id cid ^^ P.comma ^^^ pp pe)

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
  | Carray       -> !^"A.mk_array" ^^^ pp_array ()
  | Civmax       -> !^"A.ivmax" ^^^ pp_args P.space
  | Civmin       -> !^"A.ivmin" ^^^ pp_args P.space
  | Civsizeof    -> !^"M.sizeof_ival" ^^^ pp_args P.space
  | Civalignof   -> !^"M.alignof_ival" ^^^ pp_args P.space
  | Cspecified   -> !^"A.Specified" ^^^ pp_args P.space
  | Cunspecified -> !^"A.Unspecified" ^^^ pp_args P.space
  | CivCOMPL     -> !^"A.ivcompl" ^^^ pp_args P.space
  | CivAND       -> !^"A.ivand" ^^^ pp_args P.space
  | CivOR        -> !^"A.ivor" ^^^ pp_args P.space
  | CivXOR       -> !^"A.ivxor" ^^^ pp_args P.space
  | Cfvfromint   -> !^"A.fvfromint" ^^^ pp_args P.space
  | Civfromfloat -> !^"A.ivfromfloat" ^^^ pp_args P.comma


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
        traise ^^^ P.parens (!^"A.Undefined" ^^^ P.dquotes
                               (!^(Undefined.stringFromUndefined_behaviour ub)))
      | PEerror (str, pe) ->
        traise ^^^ P.parens (!^"A.Error" ^^^ P.dquotes (!^str ^^^ pp pe))
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
        P.parens (print_raw_symbol s ^^^ print_list (print_tag pp) tags)
      | PEunion (s, cid, pe) ->
        P.parens (print_raw_symbol s ^^^ print_tag pp (cid, pe))
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
    end
  in pp None pe

let print_memop globs memop pes =
  (match memop with
   | Mem_common.PtrEq -> !^"A.eq_ptrval"
   | Mem_common.PtrNe -> !^"A.ne_ptrval"
   | Mem_common.PtrGe -> !^"A.ge_ptrval"
   | Mem_common.PtrLt -> !^"A.lt_ptrval"
   | Mem_common.PtrGt -> !^"A.gt_ptrval"
   | Mem_common.PtrLe -> !^"A.le_ptrval"
   | Mem_common.Ptrdiff -> !^"A.diff_ptrval"
   | Mem_common.IntFromPtr -> !^"A.intcast_ptrval"
   | Mem_common.PtrFromInt -> !^"A.ptrvast_ival"
   | Mem_common.PtrValidForDeref -> !^"A.valid_for_deref_ptrval"
   | Mem_common.Memcmp -> !^"A.memcmp"
   | Mem_common.Memcpy -> !^"A.memcpy"
   | Mem_common.Realloc -> !^"A.realloc"
   | Mem_common.PtrWellAligned -> !^"A.ptr_well_aligned"
  ) ^^^ (P.separate_map P.space (P.parens % print_pure_expr globs)) pes

let choose_load_type pe =
  match pe with
  | (Pexpr (_, _, PEval cty)) ->
    begin match cty with
      | Vctype (Basic0 (Integer ity)) ->
        !^"A.load_integer" ^^^ P.parens (print_ail_integer_type ity)
      | Vctype (Pointer0 (q, cty)) ->
        !^"A.load_pointer" ^^^ P.parens (print_ail_qualifier q)
          ^^^ P.parens (print_ctype cty)
      | Vctype (Array0 (cty, n)) -> 
        !^"A.load_array"
          ^^^ P.parens (print_ctype cty)
          ^^^ P.parens (print_option print_num n)
      | Vctype (Struct0 s) ->
        !^"A.load_struct" ^^^ P.parens (print_raw_symbol s)
      | Vctype (Union0 s) ->
        !^"A.load_union" ^^^ P.parens (print_raw_symbol s)
      | _ -> raise (Unsupported "load not implemented")
    end
  | _ -> raise (Unsupported "load type not implemented")

let print_store_array_type = function
  | Basic0 (Integer ity) ->
    !^"A.store_array_of_int" ^^^ P.parens (print_ail_integer_type ity)
  | Pointer0 (q, cty) ->
    !^"A.store_array_of_ptr" ^^^ P.parens (print_ail_qualifier q)
      ^^^ P.parens (print_ctype cty)
  | _ -> raise (Unsupported "store array not implemented")

let choose_store_type pe =
  match pe with
  | (Pexpr (_, _, PEval cty)) ->
    begin match cty with
      | Vctype (Basic0 (Integer ity)) ->
        !^"A.store_integer" ^^^ P.parens (print_ail_integer_type ity)
      | Vctype (Pointer0 (q, cty)) ->
        !^"A.store_pointer" ^^^ P.parens (print_ail_qualifier q)
          ^^^ P.parens (print_ctype cty)
      | Vctype (Struct0 s) ->
        !^"A.store_struct" ^^^ P.parens (print_raw_symbol s)
      | Vctype (Union0 s) ->
        !^"A.store_union" ^^^ P.parens (print_raw_symbol s)
      | Vctype (Array0 (cty, n)) ->
        print_store_array_type cty
          ^^^ P.parens (print_option print_num n)
      | _ -> raise (Unsupported "store not implemented")
    end
  | _ -> raise (Unsupported "store not implemented")

let print_action globs act =
  match act with
  | Create (al, ty, pre) ->
    !^"A.create"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs ty)
    ^^^ tnone
  | CreateReadOnly (al, ty, x, pre) ->
    !^"A.create"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs ty)
    ^^^ P.parens (tsome ^^ P.parens (print_pure_expr globs x))
  | Alloc0 (al, n, pre) ->
    !^"A.alloc"
    ^^^ P.parens (print_symbol_prefix pre)
    ^^^ P.parens (print_pure_expr globs al)
    ^^^ P.parens (print_pure_expr globs n)
  | Kill (b, e) ->
    !^"M.kill" ^^ print_bool b ^^^ P.parens (print_pure_expr globs e)
  | Store0 (ty, pe1, pe2, _) ->
    choose_store_type ty
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
  | CpsPure pe            -> !^"A.return" ^^^ P.parens (print_pure_expr globs pe)
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
    !^"A.nd"
    ^^^ print_int (List.length ces)
    ^^^ print_list (print_control globs) ces

let print_seq = function
  | Some (CaseBase (None, _))
  | Some (CaseCtor (_, []))
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
