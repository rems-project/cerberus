open Cerb_pp_prelude
module CF = Cerb_frontend
open CF
module P = PPrint

open Mucore

(* Helper to print Coq definitions *)
let coq_def name args body =
  !^"Definition" ^^^ !^name ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."

let coq_notation name args body =
  !^"Notation" ^^^ !^("\"" ^ name ^ "\"") ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."

(* Placeholder printers for opaque types *)
let pp_annot_t _ = !^"annot_placeholder"
let pp_sctypes_t _ = !^"sctypes_placeholder" 
let pp_undefined_behaviour _ = !^"undefined_behaviour_placeholder"
let pp_memory_order _ = !^"memory_order_placeholder"
let pp_linux_memory_order _ = !^"linux_memory_order_placeholder"
let pp_polarity _ = !^"polarity_placeholder"

(* Basic type printers *)
let pp_location loc = !^"dummy_location"  (* TODO: proper location printing *)

let pp_type ty = !^"dummy_type"  (* TODO: proper type printing *)

let pp_basetype bt = !^"dummy_basetype"  (* TODO: proper basetype printing *)

let pp_list pp_elem xs = 
  !^"[" ^^^ 
  (List.fold_left (fun acc x -> 
    if acc == P.empty then pp_elem x
    else acc ^^ !^";" ^^^ pp_elem x
  ) P.empty xs) ^^^ 
  !^"]"

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
    !^(Digest.to_hex d) ^^^ 
    !^(string_of_int n) ^^^ 
    pp_symbol_description sd ^^ 
    !^")"
and pp_symbol_prefix = function
  | CF.Symbol.PrefSource(loc, syms) -> !^"(PrefSource" ^^^ pp_location loc ^^^ pp_list pp_symbol syms ^^ !^")"
  | CF.Symbol.PrefFunArg(loc, d, z) -> !^"(PrefFunArg" ^^^ pp_location loc ^^^ !^d ^^^ !^(Z.to_string (Z.of_int z)) ^^ !^")"
  | CF.Symbol.PrefStringLiteral(loc, d) -> !^"(PrefStringLiteral" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefTemporaryLifetime(loc, d) -> !^"(PrefTemporaryLifetime" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefCompoundLiteral(loc, d) -> !^"(PrefCompoundLiteral" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefMalloc -> !^"PrefMalloc"
  | CF.Symbol.PrefOther(s) -> !^"(PrefOther" ^^^ !^s ^^ !^")"

  
(* Constructor printers *)
let pp_ctor = function
  | Cnil bt -> !^"(Cnil" ^^^ pp_basetype bt ^^ !^")"
  | Ccons -> !^"Ccons"
  | Ctuple -> !^"Ctuple" 
  | Carray -> !^"Carray"

(* Operator printers *)
let pp_binop = function
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

(* Action printers *)
let rec pp_paction (Paction (pol, act)) =
  !^"{|" ^^^
  !^"paction_polarity :=" ^^^ pp_polarity pol ^^ !^";" ^^^
  !^"paction_action :=" ^^^ pp_action act ^^^
  !^"|}"

and pp_action (Action (loc, act)) =
  !^"{|" ^^^
  !^"action_location :=" ^^^ pp_location loc ^^ !^";" ^^^
  !^"action_content :=" ^^^ pp_action_content act ^^^
  !^"|}"

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
       !^"(PEop" ^^^ pp_binop op ^^^ pp_pexpr e1 ^^^ pp_pexpr e2 ^^ !^")"
   | _ -> !^"(* TODO: other pexpr cases *)")

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
  !^"ct :=" ^^^ pp_sctypes_t ct ^^^
  !^"|}"

and pp_kill_kind = function
  | Dynamic ->
      !^"Dynamic"  (* constructor with no arguments *)
  | Static ct ->
      !^"(Static" ^^^ pp_sctypes_t ct ^^ !^")"

and pp_bool b = if b then !^"true" else !^"false"
and pp_value (V (ty, v)) =
  !^"V" ^^^ pp_type ty ^^^
  (match v with
   | Vobject ov -> !^"(Vobject" ^^^ pp_object_value ov ^^ !^")"
   | Vctype t -> !^"(Vctype" ^^^ pp_type t ^^ !^")"
   | Vfunction_addr s -> !^"(Vfunction_addr" ^^^ pp_symbol s ^^ !^")"
   | Vunit -> !^"Vunit"
   | Vtrue -> !^"Vtrue"
   | Vfalse -> !^"Vfalse"
   | Vlist (bt, vs) -> 
       !^"(Vlist" ^^^ pp_basetype bt ^^^ pp_list pp_value vs ^^ !^")"
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
         pp_sctypes_t ty ^^ !^"," ^^^
         pp_mem_value v ^^ !^")") fields ^^ !^")"
   | OVunion (sym, id, v) ->
       !^"(OVunion" ^^^ pp_symbol sym ^^^
       pp_identifier id ^^^ pp_mem_value v ^^ !^")")


(* Function specification printers *)
let pp_ft ft = !^"dummy_ft"  (* TODO *)

let pp_args_and_body args = !^"dummy_args"  (* TODO *)

let pp_trusted = function
  | Trusted loc -> !^"(Trusted" ^^^ pp_location loc ^^ !^")"
  | Checked -> !^"Checked"

let rec pp_expr (Expr (loc, annots, ty, e)) =
  !^"Expr" ^^^ pp_location loc ^^^
  pp_list pp_annot_t annots ^^^ pp_type ty ^^^
  (match e with
   | Epure pe -> !^"(Epure" ^^^ pp_pexpr pe ^^ !^")"
   | Eaction pa -> !^"(Eaction" ^^^ pp_paction pa ^^ !^")"
   | Eskip -> !^"Eskip"
   | Eif (c, t, e) ->
       !^"(Eif" ^^^ pp_pexpr c ^^^ pp_expr t ^^^ pp_expr e ^^ !^")"
   (* Add other cases following same pattern *)
   | _ -> !^"(* TODO: other expr cases *)")

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
          (!^"GlobalDef" ^^^ pp_sctypes_t ct ^^^ pp_expr e) ^^ P.hardline
    | GlobalDecl ct ->
        coq_def (Pp_symbol.to_string sym) P.empty
          (!^"GlobalDecl" ^^^ pp_sctypes_t ct) ^^ P.hardline
  ) P.empty file.globs ^^

  (* Print functions *)
  !^"(* Function definitions *)" ^^ P.hardline ^^
  Pmap.fold (fun sym decl acc ->
    acc ^^
    match decl with
    | ProcDecl (loc, ft) ->
        coq_def (Pp_symbol.to_string sym) P.empty
          (!^"ProcDecl" ^^^ pp_location loc ^^^ 
           match ft with None -> !^"None" | Some ft -> !^"(Some" ^^^ pp_ft ft ^^ !^")")
    | Proc {loc; args_and_body; trusted} ->
        coq_def (Pp_symbol.to_string sym) P.empty
          (!^"Proc" ^^^ pp_location loc ^^^ pp_args_and_body args_and_body ^^^
           pp_trusted trusted)
  ) file.funs P.empty

let pp_file_string file =
  Pp_utils.to_plain_string (pp_file file) 