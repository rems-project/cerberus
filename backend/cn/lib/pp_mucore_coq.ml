[@@@warning "-32-27-26"]  (* Disable unused value warnings and unused variable warnings *)

open Cerb_pp_prelude
open Printf
module CF = Cerb_frontend
open CF
module P = PPrint

open Mucore

let pp_list pp_elem xs = 
    !^"[" ^^^ 
    (List.fold_left (fun acc x -> 
      if acc == P.empty then pp_elem x
      else acc ^^ !^";" ^^^ pp_elem x
    ) P.empty xs) ^^^ 
    !^"]"
  

let pp_option pp_elem = function
  | None -> !^"None"
  | Some x -> !^"(Some" ^^^ pp_elem x ^^ !^")"

(* Helper to print Coq definitions *)
let coq_def name args body =
  !^"Definition" ^^^ !^name ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."

let coq_notation name args body =
  !^"Notation" ^^^ !^("\"" ^ name ^ "\"") ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."

(* Placeholder printers for opaque types *)
let pp_annot_t _ = !^"annot_placeholder"
let pp_undefined_behaviour _ = !^"undefined_behaviour_placeholder"
let pp_memory_order _ = !^"memory_order_placeholder"
let pp_linux_memory_order _ = !^"linux_memory_order_placeholder"
let pp_polarity _ = !^"polarity_placeholder"
let pp_cn_condition _ = !^"cn_condition_placeholder"
let pp_return_type _ = !^"return_type_placeholder" 
let pp_label_map _ = !^"label_map_placeholder"
let pp_type _ = !^"type_placeholder"
(* TODO see if this is needed *)
let pp_basetype_loc () = !^"pointer"

(* Basic type printers *)
let pp_lexing_position {Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum} =
  !^"{"
  ^^ !^"pos_fname :=" ^^ !^(sprintf "%S" pos_fname) ^^ !^";"
  ^^ !^"pos_lnum :=" ^^ !^(string_of_int pos_lnum) ^^ !^";"
  ^^ !^"pos_bol :=" ^^ !^(string_of_int pos_bol) ^^ !^";"
  ^^ !^"pos_cnum :=" ^^ !^(string_of_int pos_cnum)
  ^^ !^"}"

let pp_location_cursor = function
  | Cerb_location.NoCursor -> !^"NoCursor"
  | Cerb_location.PointCursor pos -> !^"(PointCursor" ^^^ pp_lexing_position pos ^^ !^")"
  | Cerb_location.RegionCursor (start_pos, end_pos) -> 
      !^"(RegionCursor" ^^^ pp_lexing_position start_pos ^^^
      pp_lexing_position end_pos ^^ !^")"

(* temporary debug option to disable noisy locations *)
let debug_print_locations = false  (* Set to true to print actual locations *)

let pp_location = function
  | Cerb_location.Loc_unknown -> !^"Loc_unknown"
  | _ when not debug_print_locations -> !^"Loc_unknown"
  | Cerb_location.Loc_other s -> !^"(Loc_other" ^^^ !^(sprintf "%S" s) ^^ !^")"
  | Cerb_location.Loc_point pos -> !^"(Loc_point" ^^^ pp_lexing_position pos ^^ !^")"
  | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
      !^"(Loc_region" ^^^ pp_lexing_position start_pos ^^^
      pp_lexing_position end_pos ^^^ pp_location_cursor cursor ^^ !^")"
  | Cerb_location.Loc_regions (pos_list, cursor) ->
      let pp_pos_pair (start_pos, end_pos) =
        !^"(" ^^ pp_lexing_position start_pos ^^ !^"," ^^^
        pp_lexing_position end_pos ^^ !^")" in
      !^"(Loc_regions" ^^^ !^"[" ^^
      P.separate_map (!^";" ^^ P.break 1) pp_pos_pair pos_list ^^
      !^"]" ^^^ pp_location_cursor cursor ^^ !^")"

(* Value printers *)
let pp_integer_value i = !^"dummy_integer"  (* TODO *)

let pp_floating_value f = !^"dummy_float"  (* TODO *)

let pp_pointer_value p = !^"dummy_pointer"  (* TODO *)

let pp_mem_value m = !^"dummy_memval"  (* TODO *)

let pp_identifier id = !^"dummy_id"  (* TODO *)


let rec pp_symbol_description = function
  | CF.Symbol.SD_None -> !^"SD_None"
  | CF.Symbol.SD_unnamed_tag loc -> !^"(SD_unnamed_tag" ^^^ pp_location loc ^^ !^")"
  | CF.Symbol.SD_Id s -> !^"(SD_Id" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_CN_Id s -> !^"(SD_CN_Id" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_ObjectAddress s -> !^"(SD_ObjectAddress" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_Return -> !^"SD_Return"
  | CF.Symbol.SD_FunArgValue s -> !^"(SD_FunArgValue" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_FunArg(loc, n) -> !^"(SD_FunArg" ^^^ pp_location loc ^^^ !^(string_of_int n) ^^ !^")"
and pp_symbol (CF.Symbol.Symbol(d, n, sd)) = 
    !^"(Symbol" ^^^ 
    !^("\"" ^ Digest.to_hex d ^ "\"") ^^^ 
    !^(string_of_int n) ^^^ 
    pp_symbol_description sd ^^ 
    !^")"
and pp_symbol_prefix = function
  | CF.Symbol.PrefSource(loc, syms) -> !^"(PrefSource" ^^^ pp_location loc ^^^ pp_list pp_symbol syms ^^ !^")"
  | CF.Symbol.PrefFunArg(loc, d, z) -> 
    let d = "arg" in (* TODO: it looks like `d` contains some garbage*)
      !^"(PrefFunArg" ^^^ pp_location loc ^^^ !^("\"" ^ d ^ "\"") ^^^ !^(Z.to_string (Z.of_int z)) ^^ !^")"
  | CF.Symbol.PrefStringLiteral(loc, d) -> !^"(PrefStringLiteral" ^^^ pp_location loc ^^^ !^("\"" ^ d ^ "\"") ^^ !^")"
  | CF.Symbol.PrefTemporaryLifetime(loc, d) -> !^"(PrefTemporaryLifetime" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefCompoundLiteral(loc, d) -> !^"(PrefCompoundLiteral" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefMalloc -> !^"PrefMalloc"
  | CF.Symbol.PrefOther(s) -> !^"(PrefOther" ^^^ !^s ^^ !^")"


  let rec pp_basetype pp_loc = function
  | BaseTypes.Unit -> !^"Unit"
  | BaseTypes.Bool -> !^"Bool"
  | BaseTypes.Integer -> !^"Integer"
  | BaseTypes.MemByte -> !^"MemByte"
  | BaseTypes.Bits (sign, n) -> 
      !^"(Bits" ^^^ 
      (match sign with 
       | BaseTypes.Signed -> !^"Signed"
       | BaseTypes.Unsigned -> !^"Unsigned") ^^^
      !^(string_of_int n) ^^ !^")"
  | BaseTypes.Real -> !^"Real"
  | BaseTypes.Alloc_id -> !^"Alloc_id"
  | BaseTypes.CType -> !^"CType"
  | BaseTypes.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Datatype sym -> !^"(Datatype" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Record fields -> 
      !^"(Record" ^^^ P.separate_map (!^";" ^^ P.break 1)
        (fun (id, ty) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_basetype pp_loc ty ^^ !^")") 
        fields ^^ !^")"
  | BaseTypes.Map (t1, t2) -> !^"(Map" ^^^ pp_basetype pp_loc t1 ^^^ pp_basetype pp_loc t2 ^^ !^")"
  | BaseTypes.List t -> !^"(List" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Tuple ts -> !^"(Tuple" ^^^ P.separate_map (!^";" ^^ P.break 1) (pp_basetype pp_loc) ts ^^ !^")"
  | BaseTypes.Set t -> !^"(TSet" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Loc x -> pp_loc x

  let pp_integer_base_type = function
  | Sctypes.IntegerBaseTypes.Ichar -> !^"Ichar"
  | Sctypes.IntegerBaseTypes.Short -> !^"Short"
  | Sctypes.IntegerBaseTypes.Int_ -> !^"Int_"
  | Sctypes.IntegerBaseTypes.Long -> !^"Long"
  | Sctypes.IntegerBaseTypes.LongLong -> !^"LongLong"
  | Sctypes.IntegerBaseTypes.IntN_t n -> !^"(IntN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Int_leastN_t n -> !^"(Int_leastN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Int_fastN_t n -> !^"(Int_fastN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Intmax_t -> !^"Intmax_t"
  | Sctypes.IntegerBaseTypes.Intptr_t -> !^"Intptr_t"

let pp_integer_type = function
  | Sctypes.IntegerTypes.Char -> !^"Char"
  | Sctypes.IntegerTypes.Bool -> !^"Bool"
  | Sctypes.IntegerTypes.Signed ibt -> !^"(Signed" ^^^ pp_integer_base_type ibt ^^ !^")"
  | Sctypes.IntegerTypes.Unsigned ibt -> !^"(Unsigned" ^^^ pp_integer_base_type ibt ^^ !^")"
  | Sctypes.IntegerTypes.Enum sym -> !^"(Enum" ^^^ pp_symbol sym ^^ !^")"
  | Sctypes.IntegerTypes.Wchar_t -> !^"Wchar_t"
  | Sctypes.IntegerTypes.Wint_t -> !^"Wint_t"
  | Sctypes.IntegerTypes.Size_t -> !^"Size_t"
  | Sctypes.IntegerTypes.Ptrdiff_t -> !^"Ptrdiff_t"
  | Sctypes.IntegerTypes.Ptraddr_t -> !^"Ptraddr_t"


  let rec pp_ctype (Ctype.Ctype (annots, ct)) =
    !^"(Ctype" ^^^
    pp_list pp_annot_t annots ^^^
    (match ct with
    | Ctype.Void -> !^"Void"
    | Ctype.Basic bt -> !^"(Basic" ^^^ pp_basic_type bt ^^ !^")"
    | Ctype.Array (ct, None) -> !^"(Array" ^^^ pp_ctype ct ^^^ !^"None" ^^ !^")"
    | Ctype.Array (ct, Some n) -> !^"(Array" ^^^ pp_ctype ct ^^^ !^"(Some" ^^^ !^(Z.to_string n) ^^ !^"))" ^^ !^")"
    | Ctype.Function ((quals, ret), args, variadic) ->
        !^"(Function" ^^^
        !^"(" ^^^ pp_qualifiers quals ^^ !^"," ^^^ pp_ctype ret ^^ !^")" ^^^
        pp_list (fun (q, ct, is_reg) -> 
          !^"(" ^^ pp_qualifiers q ^^ !^"," ^^^ pp_ctype ct ^^ !^"," ^^^ !^(string_of_bool is_reg) ^^ !^")") args ^^^
        !^(string_of_bool variadic) ^^ !^")"
    | Ctype.FunctionNoParams (quals, ret) ->
        !^"(FunctionNoParams" ^^^
        !^"(" ^^^ pp_qualifiers quals ^^ !^"," ^^^ pp_ctype ret ^^ !^"))"
    | Ctype.Pointer (quals, ct) ->
        !^"(Pointer" ^^^ pp_qualifiers quals ^^^ pp_ctype ct ^^ !^")"
    | Ctype.Atomic ct -> !^"(Atomic" ^^^ pp_ctype ct ^^ !^")"
    | Ctype.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
    | Ctype.Union sym -> !^"(Union" ^^^ pp_symbol sym ^^ !^")") ^^
    !^")"
  
  and pp_basic_type = function
    | Ctype.Integer it -> !^"(Integer" ^^^ pp_integer_type it ^^ !^")"
    | Ctype.Floating ft -> !^"(Floating" ^^^ pp_floating_type ft ^^ !^")"
  
  and pp_floating_type = function
    | Ctype.RealFloating rft -> !^"(RealFloating" ^^^ pp_real_floating_type rft ^^ !^")"
  
  and pp_real_floating_type = function
    | Ctype.Float -> !^"Float"
    | Ctype.Double -> !^"Double" 
    | Ctype.LongDouble -> !^"LongDouble"
  
  and pp_qualifiers quals =
    !^"{|" ^^^
    !^"const :=" ^^^ !^(string_of_bool quals.Ctype.const) ^^ !^";" ^^^
    !^"restrict :=" ^^^ !^(string_of_bool quals.Ctype.restrict) ^^ !^";" ^^^
    !^"volatile :=" ^^^ !^(string_of_bool quals.Ctype.volatile) ^^^
    !^"|}"
  
  
  let rec pp_sctype = function
  | Sctypes.Void -> !^"Void"
  | Sctypes.Integer it -> !^"(Integer" ^^^ pp_integer_type it ^^ !^")"
  | Sctypes.Array (ct, None) -> !^"(Array" ^^^ pp_sctype ct ^^^ !^"None" ^^ !^")"
  | Sctypes.Array (ct, Some n) -> !^"(Array" ^^^ pp_sctype ct ^^^ !^"(Some" ^^^ !^(string_of_int n) ^^ !^"))" ^^ !^")"
  | Sctypes.Pointer ct -> !^"(Pointer" ^^^ pp_sctype ct ^^ !^")"
  | Sctypes.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
  | Sctypes.Function ((quals, ret), args, variadic) ->
      !^"(SCFunction" ^^^
      !^"(" ^^^ pp_qualifiers quals ^^ !^"," ^^^ pp_sctype ret ^^ !^")" ^^^
      pp_list (fun (ct, is_reg) -> !^"(" ^^ pp_sctype ct ^^ !^"," ^^^ !^(string_of_bool is_reg) ^^ !^")") args ^^^
      !^(string_of_bool variadic) ^^ !^")"

  and pp_qualifiers quals =
    !^"{|" ^^^
    !^"const :=" ^^^ !^(string_of_bool quals.Ctype.const) ^^ !^";" ^^^
    !^"restrict :=" ^^^ !^(string_of_bool quals.Ctype.restrict) ^^ !^";" ^^^
    !^"volatile :=" ^^^ !^(string_of_bool quals.Ctype.volatile) ^^^
    !^"|}"

(* Constructor printers *)
let rec pp_core_base_type = function
  | Core.BTy_unit -> !^"BTy_unit"
  | Core.BTy_boolean -> !^"BTy_boolean"
  | Core.BTy_ctype -> !^"BTy_ctype"
  | Core.BTy_list t -> !^"(BTy_list" ^^^ pp_core_base_type t ^^ !^")"
  | Core.BTy_tuple ts -> !^"(BTy_tuple" ^^^ P.separate_map (!^";" ^^ P.break 1) pp_core_base_type ts ^^ !^")"
  | Core.BTy_object ot -> !^"(BTy_object" ^^^ pp_core_object_type ot ^^ !^")"
  | Core.BTy_loaded ot -> !^"(BTy_loaded" ^^^ pp_core_object_type ot ^^ !^")"
  | Core.BTy_storable -> !^"BTy_storable"

and pp_core_object_type = function
  | Core.OTy_integer -> !^"OTy_integer"
  | Core.OTy_floating -> !^"OTy_floating"
  | Core.OTy_pointer -> !^"OTy_pointer"
  | Core.OTy_array t -> !^"(OTy_array" ^^^ pp_core_object_type t ^^ !^")"
  | Core.OTy_struct sym -> !^"(OTy_struct" ^^^ pp_symbol sym ^^ !^")"
  | Core.OTy_union sym -> !^"(OTy_union" ^^^ pp_symbol sym ^^ !^")"

  let pp_ctor = function
  | Mucore.Cnil bt -> !^"(Cnil" ^^^ pp_core_base_type bt ^^ !^")"
  | Mucore.Ccons -> !^"Ccons"
  | Mucore.Ctuple -> !^"Ctuple" 
  | Mucore.Carray -> !^"Carray"

(* Operator printers *)
let pp_core_binop = function
  | Core.OpAdd -> !^"Add"
  | Core.OpSub -> !^"Sub"
  | Core.OpMul -> !^"Mul"
  | Core.OpDiv -> !^"Div"
  | Core.OpRem_t -> !^"Rem_t"
  | Core.OpRem_f -> !^"Rem_f"
  | Core.OpExp -> !^"Exp"
  | Core.OpEq -> !^"Eq"
  | Core.OpGt -> !^"Gt"
  | Core.OpLt -> !^"Lt"
  | Core.OpGe -> !^"Ge"
  | Core.OpLe -> !^"Le"
  | Core.OpAnd -> !^"And"
  | Core.OpOr -> !^"Or"

let pp_binop = function
  | Terms.And -> !^"And"
  | Terms.Or -> !^"Or"
  | Terms.Implies -> !^"Implies"
  | Terms.Add -> !^"Add"
  | Terms.Sub -> !^"Sub"
  | Terms.Mul -> !^"Mul"
  | Terms.MulNoSMT -> !^"MulNoSMT"
  | Terms.Div -> !^"Div"
  | Terms.DivNoSMT -> !^"DivNoSMT"
  | Terms.Exp -> !^"Exp"
  | Terms.ExpNoSMT -> !^"ExpNoSMT"
  | Terms.Rem -> !^"Rem"
  | Terms.RemNoSMT -> !^"RemNoSMT"
  | Terms.Mod -> !^"Mod"
  | Terms.ModNoSMT -> !^"ModNoSMT"
  | Terms.BW_Xor -> !^"BW_Xor"
  | Terms.BW_And -> !^"BW_And"
  | Terms.BW_Or -> !^"BW_Or"
  | Terms.ShiftLeft -> !^"ShiftLeft"
  | Terms.ShiftRight -> !^"ShiftRight"
  | Terms.LT -> !^"LT"
  | Terms.LE -> !^"LE"
  | Terms.Min -> !^"Min"
  | Terms.Max -> !^"Max"
  | Terms.EQ -> !^"EQ"
  | Terms.LTPointer -> !^"LTPointer"
  | Terms.LEPointer -> !^"LEPointer"
  | Terms.SetUnion -> !^"SetUnion"
  | Terms.SetIntersection -> !^"SetIntersection"
  | Terms.SetDifference -> !^"SetDifference"
  | Terms.SetMember -> !^"SetMember"
  | Terms.Subset -> !^"Subset"

(* Action printers *)
 
let pp_bw_binop = function
  | BW_OR -> !^"BW_OR"
  | BW_AND -> !^"BW_AND" 
  | BW_XOR -> !^"BW_XOR"

let pp_bw_unop = function
  | BW_COMPL -> !^"BW_COMPL"
  | BW_CTZ -> !^"BW_CTZ"
  | BW_FFS -> !^"BW_FFS"

let pp_iop = function
  | Core.IOpAdd -> !^"IOpAdd"
  | Core.IOpSub -> !^"IOpSub"
  | Core.IOpMul -> !^"IOpMul"
  | Core.IOpShl -> !^"IOpShl"
  | Core.IOpShr -> !^"IOpShr"

let rec pp_pattern_ = function
  | CaseBase (sym_opt, bt) ->
      !^"(CaseBase" ^^^ 
      pp_option pp_symbol sym_opt ^^^
      pp_core_base_type bt ^^ 
      !^")"
  | CaseCtor (ctor, pats) ->
      !^"(CaseCtor" ^^^ 
      pp_ctor ctor ^^^
      pp_list pp_pattern pats ^^
      !^")"

and pp_pattern (Pattern (loc, annots, ty, pat)) =
  !^"(Pattern" ^^^
  pp_location loc ^^^
  pp_list pp_annot_t annots ^^^
  pp_type ty ^^^
  pp_pattern_ pat ^^
  !^")"


let rec pp_mem_constraint = function
    Mem_common.MC_empty -> !^"MC_empty"
  | Mem_common.MC_eq (x, y) -> !^"(MC_eq" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_le (x, y) -> !^"(MC_le" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_lt (x, y) -> !^"(MC_lt" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_in_device x -> !^"(MC_in_device" ^^^ pp_integer_value x ^^ !^")"
  | Mem_common.MC_or (x, y) -> !^"(MC_or" ^^^ pp_mem_constraint x ^^^ pp_mem_constraint y ^^ !^")"
  | Mem_common.MC_conj xs -> !^"(MC_conj" ^^^ pp_list pp_mem_constraint xs ^^ !^")"
  | Mem_common.MC_not x -> !^"(MC_not" ^^^ pp_mem_constraint x ^^ !^")"

(* Action content remains inductive since it's defined as an inductive type *)
and pp_pexpr (Pexpr (loc, annots, ty, pe)) =
  !^"Pexpr" ^^^ pp_location loc ^^^
  pp_list pp_annot_t annots ^^^ pp_type ty ^^^
  (match pe with
   | PEsym s -> !^"(PEsym" ^^^ pp_symbol s ^^ !^")"
   | PEval v -> !^"(PEval" ^^^ pp_value v ^^ !^")"
   | PEctor (c, es) -> 
       !^"(PEctor" ^^^ pp_ctor c ^^^ pp_list pp_pexpr es ^^ !^")"
   | PEop (op, e1, e2) ->
       !^"(PEop" ^^^ pp_core_binop op ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | PEconstrained cs ->
       !^"(PEconstrained" ^^^ pp_list (fun (c, e) -> !^"(" ^^ pp_mem_constraint c ^^ !^"," ^^^ pp_pexpr e ^^ !^")") cs ^^ !^")"
   | PEbitwise_unop (op, e) ->
       !^"(PEbitwise_unop" ^^^ pp_bw_unop op ^^^ pp_pexpr e ^^ !^")"
   | PEbitwise_binop (op, e1, e2) ->
       !^"(PEbitwise_binop" ^^^ pp_bw_binop op ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | Cfvfromint e -> !^"(Cfvfromint" ^^^ pp_pexpr e ^^ !^")"
   | Civfromfloat (act, e) -> !^"(Civfromfloat" ^^^ pp_act act ^^^ pp_pexpr e ^^ !^")"
   | PEarray_shift (base, ct, idx) ->
       !^"(PEarray_shift" ^^^ pp_pexpr base ^^^ pp_sctype ct ^^^ pp_pexpr idx ^^ !^")"
   | PEmember_shift (e, sym, id) ->
       !^"(PEmember_shift" ^^^ pp_pexpr e ^^^ pp_symbol sym ^^^ pp_identifier id ^^ !^")"
   | PEnot e -> !^"(PEnot" ^^^ pp_pexpr e ^^ !^")"
   | PEapply_fun (f, args) ->
       !^"(PEapply_fun" ^^^ pp_function f ^^^ pp_list pp_pexpr args ^^ !^")"
   | PEstruct (sym, fields) ->
       !^"(PEstruct" ^^^ pp_symbol sym ^^^
       pp_list (fun (id, e) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_pexpr e ^^ !^")") fields ^^ !^")"
   | PEunion (sym, id, e) ->
       !^"(PEunion" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_pexpr e ^^ !^")"
   | PEcfunction e -> !^"(PEcfunction" ^^^ pp_pexpr e ^^ !^")"
   | PEmemberof (sym, id, e) ->
       !^"(PEmemberof" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_pexpr e ^^ !^")"
   | PEbool_to_integer e -> !^"(PEbool_to_integer" ^^^ pp_pexpr e ^^ !^")"
   | PEconv_int (e1, e2) -> !^"(PEconv_int" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | PEconv_loaded_int (e1, e2) -> !^"(PEconv_loaded_int" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | PEwrapI (act, e) -> !^"(PEwrapI" ^^^ pp_act act ^^^ pp_pexpr e ^^ !^")"
   | PEcatch_exceptional_condition (act, e) ->
       !^"(PEcatch_exceptional_condition" ^^^ pp_act act ^^^ pp_pexpr e ^^ !^")"
   | PEbounded_binop (kind, op, e1, e2) ->
       !^"(PEbounded_binop" ^^^ pp_bound_kind kind ^^^ pp_iop op ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | PEis_representable_integer (e, act) ->
       !^"(PEis_representable_integer" ^^^ pp_pexpr e ^^^ pp_act act ^^ !^")"
   | PEundef (loc, ub) -> !^"(PEundef" ^^^ pp_location loc ^^^ pp_undefined_behaviour ub ^^ !^")"
   | PEerror (msg, e) -> !^"(PEerror" ^^^ !^msg ^^^ pp_pexpr e ^^ !^")"
   | PElet (pat, e1, e2) -> !^"(PElet" ^^^ pp_pattern pat ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | PEif (c, t, e) -> !^"(PEif" ^^^ pp_pexpr c ^^^ pp_pexpr t ^^^ pp_pexpr e ^^ !^")"
  )
  and pp_bound_kind = function
  | Bound_Wrap act -> !^"(Bound_Wrap" ^^^ pp_act act ^^ !^")"
  | Bound_Except act -> !^"(Bound_Except" ^^^ pp_act act ^^ !^")"

  and pp_action (Action (loc, act)) =
    !^"{|" ^^^
    !^"action_location :=" ^^^ pp_location loc ^^ !^";" ^^^
    !^"action_content :=" ^^^ pp_action_content act ^^^
    !^"|}"
  
  and pp_paction (Paction (pol, act)) =
      !^"{|" ^^^
      !^"paction_polarity :=" ^^^ pp_polarity pol ^^ !^";" ^^^
      !^"paction_action :=" ^^^ pp_action act ^^^
      !^"|}"  
  and pp_action_content = function
  | Create (e, act, sym) -> 
      !^"(Create" ^^^ pp_pexpr e ^^^ pp_act act ^^^ pp_symbol_prefix sym ^^ !^")"
  | CreateReadOnly (e1, act, e2, sym) ->
      !^"(CreateReadOnly" ^^^ pp_pexpr e1 ^^^ pp_act act ^^^ 
      pp_pexpr e2 ^^^ pp_symbol_prefix sym ^^ !^")"
  | Alloc (e1, e2, sym) ->
      !^"(Alloc" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^^ pp_symbol_prefix sym ^^ !^")"
  | Kill (kind, e) ->
      !^"(Kill" ^^^ pp_kill_kind kind ^^^ pp_pexpr e ^^ !^")"
  | Store (b, act, e1, e2, mo) ->
      !^"(Store" ^^^ pp_bool b ^^^ pp_act act ^^^ pp_pexpr e1 ^^^
      pp_pexpr e2 ^^^ pp_memory_order mo ^^ !^")"
  | Load (act, e, mo) ->
      !^"(Load" ^^^ pp_act act ^^^ pp_pexpr e ^^^ pp_memory_order mo ^^ !^")"
  | RMW (act, e1, e2, e3, mo1, mo2) ->
      !^"(RMW" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^^
      pp_pexpr e3 ^^^ pp_memory_order mo1 ^^^ pp_memory_order mo2 ^^ !^")"
  | Fence mo ->
      !^"(Fence" ^^^ pp_memory_order mo ^^ !^")"
  | CompareExchangeStrong (act, e1, e2, e3, mo1, mo2) ->
      !^"(CompareExchangeStrong" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^
      pp_pexpr e2 ^^^ pp_pexpr e3 ^^^ pp_memory_order mo1 ^^^
      pp_memory_order mo2 ^^ !^")"
  | CompareExchangeWeak (act, e1, e2, e3, mo1, mo2) ->
      !^"(CompareExchangeWeak" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^
      pp_pexpr e2 ^^^ pp_pexpr e3 ^^^ pp_memory_order mo1 ^^^
      pp_memory_order mo2 ^^ !^")"
  | LinuxFence lmo ->
      !^"(LinuxFence" ^^^ pp_linux_memory_order lmo ^^ !^")"
  | LinuxLoad (act, e, lmo) ->
      !^"(LinuxLoad" ^^^ pp_act act ^^^ pp_pexpr e ^^^
      pp_linux_memory_order lmo ^^ !^")"
  | LinuxStore (act, e1, e2, lmo) ->
      !^"(LinuxStore" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^
      pp_pexpr e2 ^^^ pp_linux_memory_order lmo ^^ !^")"
  | LinuxRMW (act, e1, e2, lmo) ->
      !^"(LinuxRMW" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^
      pp_pexpr e2 ^^^ pp_linux_memory_order lmo ^^ !^")"

and pp_act {loc; annot; ct} =
  !^"{|" ^^^ 
  !^"loc :=" ^^^ pp_location loc ^^ !^";" ^^^
  !^"annot :=" ^^^ pp_list pp_annot_t annot ^^ !^";" ^^^
  !^"ct :=" ^^^ pp_sctype ct ^^^
  !^"|}"

and pp_kill_kind = function
  | Dynamic ->
      !^"Dynamic"  (* constructor with no arguments *)
  | Static ct ->
      !^"(Static" ^^^ pp_sctype ct ^^ !^")"

and pp_bool b = if b then !^"true" else !^"false"
and pp_value (V (ty, v)) =
  !^"V" ^^^ pp_type ty ^^^
  (match v with
   | Vobject ov -> !^"(Vobject" ^^^ pp_object_value ov ^^ !^")"
   | Vctype t -> !^"(Vctype" ^^^ pp_ctype t ^^ !^")"
   | Vfunction_addr s -> !^"(Vfunction_addr" ^^^ pp_symbol s ^^ !^")"
   | Vunit -> !^"Vunit"
   | Vtrue -> !^"Vtrue"
   | Vfalse -> !^"Vfalse"
   | Vlist (bt, vs) -> 
       !^"(Vlist" ^^^ pp_core_base_type bt ^^^ pp_list pp_value vs ^^ !^")"
   | Vtuple vs ->
       !^"(Vtuple" ^^^ pp_list pp_value vs ^^ !^")")
and pp_object_value (OV (ty, ov)) =
  !^"OV" ^^^ pp_type ty ^^^
  (match ov with
   | OVinteger i -> !^"(OVinteger" ^^^ pp_integer_value i ^^ !^")"
   | OVfloating f -> !^"(OVfloating" ^^^ pp_floating_value f ^^ !^")"
   | OVpointer p -> !^"(OVpointer" ^^^ pp_pointer_value p ^^ !^")"
   | OVarray vs -> 
       !^"(OVarray" ^^^ pp_list pp_object_value vs ^^ !^")"
   | OVstruct (sym, fields) ->
       !^"(OVstruct" ^^^ pp_symbol sym ^^^
       pp_list (fun (id, ty, v) -> 
         !^"(" ^^ pp_identifier id ^^ !^"," ^^^ 
         pp_sctype ty ^^ !^"," ^^^
         pp_mem_value v ^^ !^")") fields ^^ !^")"
   | OVunion (sym, id, v) ->
       !^"(OVunion" ^^^ pp_symbol sym ^^^
       pp_identifier id ^^^ pp_mem_value v ^^ !^")")


(* Function specification printers *)
let pp_ft ft = !^"dummy_ft"  (* TODO *)

let pp_location_info (loc, _) = pp_location loc


let pp_trusted = function
  | Trusted loc -> !^"(Trusted" ^^^ pp_location loc ^^ !^")"
  | Checked -> !^"Checked"


   let pp_unop = function
  | Terms.Not -> !^"Not"
  | Negate -> !^"Negate"
  | BW_CLZ_NoSMT -> !^"BW_CLZ_NoSMT"
  | BW_CTZ_NoSMT -> !^"BW_CTZ_NoSMT"
  | BW_FFS_NoSMT -> !^"BW_FFS_NoSMT"
  | BW_FLS_NoSMT -> !^"BW_FLS_NoSMT"
  | BW_Compl -> !^"BW_Compl"


let pp_sign = function
| BaseTypes.Signed -> !^"Signed"
| BaseTypes.Unsigned -> !^"Unsigned"

let rec pp_terms_pattern (Terms.Pat (pat, bt, loc)) =
  !^"(Pat" ^^^
  pp_terms_pattern_ pat ^^^
  pp_basetype pp_basetype_loc bt ^^^
  pp_location loc ^^
  !^")"
and pp_terms_pattern_ = function
  | Terms.PSym s -> !^"(PSym" ^^^ pp_symbol s ^^ !^")"
  | Terms.PWild -> !^"PWild"
  | Terms.PConstructor (sym, args) -> 
      !^"(PConstructor" ^^^ pp_symbol sym ^^^
      pp_list (fun (id, pat) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_terms_pattern pat ^^ !^")") args ^^ !^")"


let pp_const = function
  | Terms.Z z -> !^"(Z" ^^^ !^(Z.to_string z) ^^ !^")"
  | Bits ((sign, sz), z) -> !^"(Bits" ^^^ !^"(" ^^ pp_sign sign ^^ !^"," ^^^ !^(string_of_int sz) ^^ !^")" ^^^ !^(Z.to_string z) ^^ !^")"
  | Q q -> !^"(Q" ^^^ !^(Q.to_string q) ^^ !^")"
  | MemByte {alloc_id; value} -> !^"(MemByte" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string value) ^^ !^")"
  | Pointer {alloc_id; addr} -> !^"(Pointer" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string addr) ^^ !^")"
  | Alloc_id z -> !^"(Alloc_id" ^^^ !^(Z.to_string z) ^^ !^")"
  | Bool b -> !^"(Bool" ^^^ pp_bool b ^^ !^")"
  | Unit -> !^"Unit"
  | Null -> !^"Null"
  | CType_const t -> !^"(CType_const" ^^^ pp_sctype t ^^ !^")"
  | Default bt -> !^"(Default" ^^^ pp_basetype pp_basetype_loc bt ^^ !^")"

   let rec pp_index_term (IndexTerms.IT (term, bt, loc)) =
    !^"(IT" ^^^
    pp_index_term_content term ^^^
    pp_basetype pp_basetype_loc bt ^^^
    pp_location loc ^^
    !^")"
  
  and pp_index_term_content = function
    | IndexTerms.Const c -> !^"(Const" ^^^ pp_const c ^^ !^")"
    | Sym s -> !^"(Sym" ^^^ pp_symbol s ^^ !^")"
    | Unop (op, t) -> !^"(Unop" ^^^ pp_unop op ^^^ pp_index_term t ^^ !^")"
    | Binop (op, t1, t2) -> 
        !^"(Binop" ^^^ pp_binop op ^^^ pp_index_term t1 ^^^ pp_index_term t2 ^^ !^")"
    | ITE (c, t, e) ->
        !^"(ITE" ^^^ pp_index_term c ^^^ pp_index_term t ^^^ pp_index_term e ^^ !^")"
    | EachI ((n1, (sym, bt), n2), t) ->
        !^"(EachI" ^^^ !^"(" ^^^
        !^(string_of_int n1) ^^ !^"," ^^^
        !^"(" ^^ pp_symbol sym ^^ !^"," ^^^ pp_basetype pp_basetype_loc bt ^^ !^")" ^^ !^"," ^^^
        !^(string_of_int n2) ^^ !^")" ^^^
        pp_index_term t ^^ !^")"
    | Tuple ts -> !^"(Tuple" ^^^ pp_list pp_index_term ts ^^ !^")"
    | NthTuple (n, t) -> !^"(NthTuple" ^^^ !^(string_of_int n) ^^^ pp_index_term t ^^ !^")"
    | Struct (tag, members) ->
        !^"(Struct" ^^^ pp_symbol tag ^^^
        pp_list (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")") members ^^ !^")"
    | StructMember (t, member) ->
        !^"(StructMember" ^^^ pp_index_term t ^^^ pp_identifier member ^^ !^")"
    | StructUpdate ((t1, member), t2) ->
        !^"(StructUpdate" ^^^ !^"(" ^^^ pp_index_term t1 ^^ !^"," ^^^ pp_identifier member ^^ !^")" ^^^
        pp_index_term t2 ^^ !^")"
    | Record members ->
        !^"(Record" ^^^
        pp_list (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")") members ^^ !^")"
    | RecordMember (t, member) ->
        !^"(RecordMember" ^^^ pp_index_term t ^^^ pp_identifier member ^^ !^")"
    | RecordUpdate ((t1, member), t2) ->
        !^"(RecordUpdate" ^^^ !^"(" ^^^ pp_index_term t1 ^^ !^"," ^^^ pp_identifier member ^^ !^")" ^^^
        pp_index_term t2 ^^ !^")"
    | Constructor (sym, args) ->
        !^"(Constructor" ^^^ pp_symbol sym ^^^
        pp_list (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")") args ^^ !^")"
    | MemberShift (t, tag, id) ->
        !^"(MemberShift" ^^^ pp_index_term t ^^^ pp_symbol tag ^^^ pp_identifier id ^^ !^")"
    | ArrayShift {base; ct; index} ->
        !^"(ArrayShift" ^^^ pp_index_term base ^^^ pp_sctype ct ^^^ pp_index_term index ^^ !^")"
    | CopyAllocId {addr; loc} ->
        !^"(CopyAllocId" ^^^ pp_index_term addr ^^^ pp_index_term loc ^^ !^")"
    | HasAllocId t -> !^"(HasAllocId" ^^^ pp_index_term t ^^ !^")"
    | SizeOf ct -> !^"(SizeOf" ^^^ pp_sctype ct ^^ !^")"
    | OffsetOf (tag, member) ->
        !^"(OffsetOf" ^^^ pp_symbol tag ^^^ pp_identifier member ^^ !^")"
    | Nil bt -> !^"(Nil" ^^^ pp_basetype pp_basetype_loc bt ^^ !^")"
    | Cons (t1, t2) -> !^"(Cons" ^^^ pp_index_term t1 ^^^ pp_index_term t2 ^^ !^")"
    | Head t -> !^"(Head" ^^^ pp_index_term t ^^ !^")"
    | Tail t -> !^"(Tail" ^^^ pp_index_term t ^^ !^")"
    | NthList (i, xs, d) ->
        !^"(NthList" ^^^ pp_index_term i ^^^ pp_index_term xs ^^^ pp_index_term d ^^ !^")"
    | ArrayToList (arr, i, len) ->
        !^"(ArrayToList" ^^^ pp_index_term arr ^^^ pp_index_term i ^^^ pp_index_term len ^^ !^")"
    | Representable (ct, t) ->
        !^"(Representable" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
    | Good (ct, t) -> !^"(Good" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
    | Aligned {t; align} ->
        !^"(Aligned" ^^^ pp_index_term t ^^^ pp_index_term align ^^ !^")"
    | WrapI (ct, t) -> !^"(WrapI" ^^^ pp_integer_type ct ^^^ pp_index_term t ^^ !^")"
    | MapConst (bt, t) -> !^"(MapConst" ^^^ pp_basetype pp_basetype_loc bt ^^^ pp_index_term t ^^ !^")"
    | MapSet (m, k, v) ->
        !^"(MapSet" ^^^ pp_index_term m ^^^ pp_index_term k ^^^ pp_index_term v ^^ !^")"
    | MapGet (m, k) -> !^"(MapGet" ^^^ pp_index_term m ^^^ pp_index_term k ^^ !^")"
    | MapDef ((sym, bt), t) ->
        !^"(MapDef" ^^^ !^"(" ^^^ pp_symbol sym ^^ !^"," ^^^ pp_basetype pp_basetype_loc bt ^^ !^")" ^^^
        pp_index_term t ^^ !^")"
    | Apply (sym, args) ->
        !^"(Apply" ^^^ pp_symbol sym ^^^ pp_list pp_index_term args ^^ !^")"
    | Let ((sym, t1), t2) ->
        !^"(Let" ^^^ !^"(" ^^^ pp_symbol sym ^^ !^"," ^^^ pp_index_term t1 ^^ !^")" ^^^
        pp_index_term t2 ^^ !^")"
    | Match (t, cases) ->
        !^"(Match" ^^^ pp_index_term t ^^^
        pp_list (fun (pat, body) -> !^"(" ^^ pp_terms_pattern pat ^^ !^"," ^^^ pp_index_term body ^^ !^")") cases ^^ !^")"
    | Cast (bt, t) -> !^"(Cast" ^^^ pp_basetype pp_basetype_loc bt ^^^ pp_index_term t ^^ !^")"


    let pp_request_init = function
    | Request.Init -> !^"Init"
    | Request.Uninit -> !^"Uninit"
  let rec pp_request = function
    | Request.P pred ->
        !^"(P" ^^^
        !^"{|" ^^^
        !^"name :=" ^^^ pp_request_name pred.Request.Predicate.name ^^ !^";" ^^^
        !^"pointer :=" ^^^ pp_index_term pred.pointer ^^ !^";" ^^^
        !^"iargs :=" ^^^ pp_list pp_index_term pred.iargs ^^^
        !^"|}" ^^
        !^")"
    | Request.Q qpred ->
        !^"(Q" ^^^
        !^"{|" ^^^
        !^"name :=" ^^^ pp_request_name qpred.Request.QPredicate.name ^^ !^";" ^^^
        !^"pointer :=" ^^^ pp_index_term qpred.pointer ^^ !^";" ^^^
        !^"q :=" ^^^ !^"(" ^^ pp_symbol (fst qpred.q) ^^ !^"," ^^^ pp_basetype pp_basetype_loc (snd qpred.q) ^^ !^")" ^^ !^";" ^^^
        !^"q_loc :=" ^^^ pp_location qpred.q_loc ^^ !^";" ^^^
        !^"step :=" ^^^ pp_index_term qpred.step ^^ !^";" ^^^
        !^"permission :=" ^^^ pp_index_term qpred.permission ^^ !^";" ^^^
        !^"iargs :=" ^^^ pp_list pp_index_term qpred.iargs ^^^
        !^"|}" ^^
        !^")"
  and pp_request_name = function
    | Request.PName sym -> !^"(PName" ^^^ pp_symbol sym ^^ !^")"
    | Request.Owned (ct, init) -> 
      (* TODO
        !^"(Owned" ^^^ pp_sctype ct ^^^ pp_request_init init ^^ !^")"
        *)  
        P.empty
  
let pp_memop = function
        | PtrEq (e1, e2) -> !^"(PtrEq" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | PtrNe (e1, e2) -> !^"(PtrNe" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | PtrLt (e1, e2) -> !^"(PtrLt" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | PtrGt (e1, e2) -> !^"(PtrGt" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | PtrLe (e1, e2) -> !^"(PtrLe" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | PtrGe (e1, e2) -> !^"(PtrGe" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | Ptrdiff (act, e1, e2) -> !^"(Ptrdiff" ^^^ pp_act act ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | IntFromPtr (act1, act2, e) -> !^"(IntFromPtr" ^^^ pp_act act1 ^^^ pp_act act2 ^^^ pp_pexpr e ^^ !^")"
        | PtrFromInt (act1, act2, e) -> !^"(PtrFromInt" ^^^ pp_act act1 ^^^ pp_act act2 ^^^ pp_pexpr e ^^ !^")"
        | PtrValidForDeref (act, e) -> !^"(PtrValidForDeref" ^^^ pp_act act ^^^ pp_pexpr e ^^ !^")"
        | PtrWellAligned (act, e) -> !^"(PtrWellAligned" ^^^ pp_act act ^^^ pp_pexpr e ^^ !^")"
        | PtrArrayShift (e1, act, e2) -> !^"(PtrArrayShift" ^^^ pp_pexpr e1 ^^^ pp_act act ^^^ pp_pexpr e2 ^^ !^")"
        | PtrMemberShift (sym, id, e) -> !^"(PtrMemberShift" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_pexpr e ^^ !^")"
        | Memcpy (e1, e2, e3) -> !^"(Memcpy" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^^ pp_pexpr e3 ^^ !^")"
        | Memcmp (e1, e2, e3) -> !^"(Memcmp" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^^ pp_pexpr e3 ^^ !^")"
        | Realloc (e1, e2, e3) -> !^"(Realloc" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^^ pp_pexpr e3 ^^ !^")"
        | Va_start (e1, e2) -> !^"(Va_start" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
        | Va_copy e -> !^"(Va_copy" ^^^ pp_pexpr e ^^ !^")"
        | Va_arg (e, act) -> !^"(Va_arg" ^^^ pp_pexpr e ^^^ pp_act act ^^ !^")"
        | Va_end e -> !^"(Va_end" ^^^ pp_pexpr e ^^ !^")"
        | CopyAllocId (e1, e2) -> !^"(CopyAllocId" ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
      
let rec pp_expr (Expr (loc, annots, ty, e)) =
          !^"Expr" ^^^ pp_location loc ^^^
          pp_list pp_annot_t annots ^^^ pp_type ty ^^^
          (match e with
           | Epure pe -> !^"(Epure" ^^^ pp_pexpr pe ^^ !^")"
           | Ememop m -> !^"(Ememop" ^^^ pp_memop m ^^ !^")"
           | Eaction pa -> !^"(Eaction" ^^^ pp_paction pa ^^ !^")"
           | Eskip -> !^"Eskip"
           | Eccall (act, f, args) ->
               !^"(Eccall" ^^^ pp_act act ^^^ pp_pexpr f ^^^ pp_list pp_pexpr args ^^ !^")"
           | Elet (pat, e1, e2) ->
               !^"(Elet" ^^^ pp_pattern pat ^^^ pp_pexpr e1 ^^^ pp_expr e2 ^^ !^")"
           | Eunseq exprs ->
               !^"(Eunseq" ^^^ pp_list pp_expr exprs ^^ !^")"
           | Ewseq (pat, e1, e2) ->
               !^"(Ewseq" ^^^ pp_pattern pat ^^^ pp_expr e1 ^^^ pp_expr e2 ^^ !^")"
           | Esseq (pat, e1, e2) ->
               !^"(Esseq" ^^^ pp_pattern pat ^^^ pp_expr e1 ^^^ pp_expr e2 ^^ !^")"
           | Eif (c, t, e) ->
               !^"(Eif" ^^^ pp_pexpr c ^^^ pp_expr t ^^^ pp_expr e ^^ !^")"
           | Ebound e ->
               !^"(Ebound" ^^^ pp_expr e ^^ !^")"
           | End exprs ->
               !^"(End" ^^^ pp_list pp_expr exprs ^^ !^")"
           | Erun (sym, args) ->
               !^"(Erun" ^^^ pp_symbol sym ^^^ pp_list pp_pexpr args ^^ !^")"
           | CN_progs (stmts, progs) ->
              (* TODO: this constructor was omitted from the original code *)
              P.empty)
            
        
let pp_logical_constraint = function
        | LogicalConstraints.T term -> 
            !^"(T" ^^^ pp_index_term term ^^ !^")"
        | LogicalConstraints.Forall ((sym, bt), term) ->
            !^"(Forall" ^^^ !^"(" ^^^ pp_symbol sym ^^ !^"," ^^^ pp_basetype pp_basetype_loc bt ^^ !^")" ^^^
            pp_index_term term ^^ !^")"
      
   let pp_args_and_body args =
    (* args is of type arguments (expr * label_map * return_type) *)
    let rec pp_args = function
      | Computational ((sym, bt), loc, rest) ->
          !^"(Computational" ^^^
          !^"(" ^^^ pp_symbol sym ^^ !^"," ^^^ pp_basetype pp_basetype_loc bt ^^ !^")" ^^^
          pp_location_info loc ^^^
          pp_args rest ^^ !^")"
      | L logical_args -> pp_logical_args logical_args
  
    and pp_logical_args = function
      | Define ((sym, term), info, rest) ->
          !^"(Define" ^^^
          !^"(" ^^^ pp_symbol sym ^^ !^"," ^^^ pp_index_term term ^^ !^")" ^^^
          pp_location_info info ^^^
          pp_logical_args rest ^^ !^")"
      | Resource ((sym, (req, bt)), info, rest) ->
          !^"(Resource" ^^^
          !^"(" ^^^ pp_request req ^^ !^"," ^^^ pp_basetype pp_basetype_loc bt ^^ !^"))" ^^^
          pp_location_info info ^^^
          pp_logical_args rest ^^ !^")"
      | Constraint (lc, info, rest) ->
          !^"(Constraint" ^^^
          pp_logical_constraint lc ^^^
          pp_location_info info ^^^
          pp_logical_args rest ^^ !^")"
      | I (body, labels, rt) ->
          !^"(I" ^^^
          !^"(" ^^^
          pp_expr body ^^ !^"," ^^^
          pp_label_map labels ^^ !^"," ^^^
          pp_return_type rt ^^
          !^"))"
    in
    pp_args args

let pp_desugared_spec {accesses; requires; ensures} =
  !^"{|" ^^^
  !^"accesses :=" ^^^ pp_list (fun (sym, ty) -> !^"(" ^^ pp_symbol sym ^^ !^"," ^^^ pp_ctype ty ^^ !^")") accesses ^^ !^";" ^^^
  !^"requires :=" ^^^ pp_list pp_cn_condition requires ^^ !^";" ^^^
  !^"ensures :=" ^^^ pp_list pp_cn_condition ensures ^^^
  !^"|}"

(* Top-level file printer *)
let pp_file file =
  !^"Require Import MuCore." ^^ P.hardline ^^
  !^"Import MuCore." ^^ P.hardline ^^ P.hardline ^^
  
  (* Print globals *)
  !^"(* Global definitions *)" ^^ P.hardline ^^
  List.fold_left (fun acc (sym, glob) ->
    acc ^^ 
    match glob with
    | GlobalDef (ct, e) ->
        coq_def (Pp_symbol.to_string sym) P.empty
          (!^"GlobalDef" ^^^ pp_sctype ct ^^^ pp_expr e) ^^ P.hardline
    | GlobalDecl ct ->
        coq_def (Pp_symbol.to_string sym) P.empty
          (!^"GlobalDecl" ^^^ pp_sctype ct) ^^ P.hardline
  ) P.empty file.globs ^^

  (* Print functions *)
  !^"(* Function definitions *)" ^^ P.hardline ^^
  Pmap.fold (fun sym decl acc ->
    acc ^^
    match decl with
    (* TODO: handle ProcDecl *)
    | ProcDecl (loc, ft) ->
      (*
        coq_def (Pp_symbol.to_string_pretty_cn sym) P.empty
          (!^"ProcDecl" ^^^ pp_location loc ^^^ 
           match ft with None -> !^"None" | Some ft -> !^"(Some" ^^^ pp_ft ft ^^ !^")")
      *) 
      P.empty
    | Proc {loc; args_and_body; trusted; desugared_spec} ->
        coq_def (Pp_symbol.to_string_pretty_cn sym) P.empty
          (!^"Proc" ^^^ pp_location loc ^^^ pp_args_and_body args_and_body ^^^
           pp_trusted trusted ^^^ pp_desugared_spec desugared_spec)
  ) file.funs P.empty

let pp_file_string file =
  Pp_utils.to_plain_string (pp_file file) 



