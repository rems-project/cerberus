open Mucore
open Pp_mucore
open Pp_standard_typ
open Basic_standard_typ

let string_of_mucore_object_type oTy =
  Pp_utils.to_plain_string (pp_object_type oTy)
let string_of_core_base_type bTy =
  Pp_utils.to_plain_string (pp_core_base_type bTy)
let string_of_value cval =
  Pp_utils.to_plain_string (pp_value cval)
let string_of_action act =
  Pp_utils.to_plain_string (pp_action act)
let string_of_pexpr pe =
  Pp_utils.to_plain_string (pp_pexpr None pe)
let string_of_expr e =
  Pp_utils.to_plain_string (pp_expr None e)
let string_of_file f =
  Pp_utils.to_plain_string (pp_file None f)

let string_of_params z =
  Pp_utils.to_plain_string (pp_params z)
(* let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def) *)

(* let mk_string_of_continuation_element = function
 *   | Kunseq (_, es1, es2) ->
 *       fun z ->
 *         let str1 = List.fold_right (fun e acc -> string_of_expr e ^ " || " ^ acc) es1 "" in
 *         let str2 = List.fold_right (fun e acc -> acc ^ "|| " ^ string_of_expr e) es2 "" in
 *         "[ " ^ str1 ^ z ^ str2 ^ " ]"
 *   | Kwseq (_, _as, e) ->
 *       fun z ->
 *         let str = string_of_expr e in
 *         "let weak TODO = " ^ z ^ " in " ^ str
 *   | Ksseq (_, _as, e) ->
 *       fun z ->
 *         let str = string_of_expr e in
 *         "let strong TODO = " ^ z ^ " in " ^ str
 * 
 * let string_of_continuation cont =
 *   List.fold_left (fun acc cont_elem -> mk_string_of_continuation_element cont_elem acc) "[]" cont
 * 
 * 
 * let rec string_of_stack sk =
 *   Pp_utils.to_plain_string (pp_stack sk) *)
