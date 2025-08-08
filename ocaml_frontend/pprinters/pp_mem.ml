open Cerb_pp_prelude

open Mem_common

let pp_unaryOperator (o:AilSyntax.unaryOperator) =
  match o with
  | Plus -> !^ "Plus"
  | Minus -> !^ "Minus"
  | Bnot -> !^ "Bnot"
  | Address -> !^ "Address"
  | Indirection -> !^ "Indirection"
  | PostfixIncr -> !^ "PostfixIncr"
  | PostfixDecr -> !^ "PostfixDecr"

let pp_derivecap_op = function
  | DCunary u -> pp_unaryOperator u
  | DCbinary b -> !^ "TODO:binary"

let pp_pure_memop = function
  | DeriveCap (bop, is_signed) ->
      !^ "DeriveCap" ^^ P.brackets (pp_derivecap_op bop)
  | CapAssignValue ->
      !^ "CapAssignValue"
  | Ptr_tIntValue ->
      !^ "Ptr_tIntValue"
  | ByteFromInt ->
      !^"ByteFromInt"
  | IntFromByte ->
      !^"IntFromByte"

let pp_memop = function
  | PtrEq ->
      !^ "PtrEq"
  | PtrNe ->
      !^ "PtrNe"
  | PtrLt ->
      !^ "PtrLt"
  | PtrGt ->
      !^ "PtrGt"
  | PtrLe ->
      !^ "PtrLe"
  | PtrGe ->
      !^ "PtrGe"
  | Ptrdiff ->
      !^ "Ptrdiff"
  | IntFromPtr ->
      !^ "IntFromPtr"
  | PtrFromInt ->
      !^ "PtrFromInt"
  | PtrValidForDeref ->
      !^ "PtrValidForDeref"
  | PtrWellAligned ->
      !^ "PtrWellAligned"
  | Memcmp ->
      !^ "Memcmp"
  | Memcpy ->
      !^ "Memcpy"
  | Realloc ->
      !^ "Realloc"
  | Va_start ->
      !^ "Va_start"
  | Va_copy ->
      !^ "Va_copy"
  | Va_arg ->
      !^ "Va_arg"
  | Va_end ->
      !^ "Va_end"
  | PtrArrayShift ->
      !^ "PtrArrayShift"
  | PtrMemberShift (tag_sym, membr_ident) ->
      !^ "PtrArrayShift" ^^ P.brackets (!^ (Pp_symbol.to_string_pretty tag_sym) ^^ P.comma ^^^ Pp_symbol.pp_identifier membr_ident)
  | Copy_alloc_id ->
      !^ "Copy_alloc_id"
  | CHERI_intrinsic (str, (ret_ty, tys)) ->
      let fun_ty = Ctype.(Ctype ([], Function ((no_qualifiers, ret_ty), List.map (fun ty -> (no_qualifiers, ty, false)) tys, false))) in
      !^ ("cheri_" ^ str) ^^ P.brackets (P.squotes (Pp_core_ctype.pp_ctype fun_ty))


(* let pp_pointer_shift = Impl.pp_pointer_shift *)
(*
let pp_pointer_value = failwith "Impl.pp_pointer_value"
let pp_integer_value = failwith "Impl.pp_integer_value"
let pp_integer_value_for_core = failwith "Impl.pp_integer_value_for_core"
let pp_mem_value = failwith "Impl.pp_mem_value"
let pp_pretty_pointer_value = failwith "Impl.pp_pretty_pointer_value"
let pp_pretty_integer_value = failwith "Impl.pp_pretty_integer_value"
let pp_pretty_mem_value = failwith "Impl.pp_pretty_mem_value"
*)

(* let rec pp_raw_mem_constraint pp constr =
  P.parens begin match constr with
    | MC_empty ->
        P.empty
    | MC_eq (cs1, cs2) ->
        P.equals ^^^ pp cs1 ^^^ pp cs2
    | MC_le (cs1, cs2) ->
        P.langle ^^ P.equals ^^^ pp cs1 ^^^ pp cs2
    | MC_lt (cs1, cs2) ->
        P.langle ^^^ pp cs1 ^^^ pp cs2
    | MC_in_device a ->
        !^ "in_device_mem" ^^^ pp a
    | MC_or (cs1, cs2) ->
        !^ "or" ^^^ pp_raw_mem_constraint pp cs1 ^^^ pp_raw_mem_constraint pp cs2
    | MC_conj css ->
        !^ "and" ^^^ P.flow (P.break 1) (List.map (pp_raw_mem_constraint pp) css)
    | MC_not cs ->
        !^ "not" ^^^ pp_raw_mem_constraint pp cs
  end *)

let pp_mem_constraint pp constr =
  let prec = function
    | MC_empty
    | MC_in_device _ ->
        None
    | MC_eq _ ->
        Some 1
    | MC_le _
    | MC_lt _ ->
        Some 2
    | MC_not _ ->
        Some 3
    | MC_conj _ ->
        Some 4
    | MC_or _ ->
        Some 5 in
  let compare_precedence p1 p2 =
    match (p1, p2) with
      | (Some n1, Some n2) -> n1 <= n2
      | _                  -> true
  in
  let rec aux outer_prec constr =
    let p = prec constr in
    (if compare_precedence p outer_prec then fun z -> z else P.parens)
     begin match constr with
      | MC_empty ->
          P.empty
      | MC_eq (cs1, cs2) ->
          pp cs1 ^^^ P.equals ^^^ pp cs2
      | MC_le (cs1, cs2) ->
          pp cs1 ^^^ P.langle ^^ P.equals ^^^ pp cs2
      | MC_lt (cs1, cs2) ->
          pp cs1 ^^^ P.langle ^^^ pp cs2
      | MC_in_device a ->
          !^ "in_device_mem" ^^^ P.parens (pp a)
      | MC_or (cs1, cs2) ->
          aux p cs1 ^^^ !^ "\\/" ^^^ aux p cs2
      | MC_conj css ->
          P.flow (P.break 1 ^^ !^ "/\\" ^^ P.break 1) (List.map (aux p) css)
      | MC_not cs ->
          !^ "not" ^^ P.parens (aux p cs)
    end in
  aux None constr
