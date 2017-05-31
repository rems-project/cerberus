open Core
open Pp_core

let string_of_core_object_type oTy =
  Pp_utils.to_plain_string (pp_core_object_type oTy)
let string_of_core_base_type bTy =
  Pp_utils.to_plain_string (pp_core_base_type bTy)
let string_of_value cval =
  Pp_utils.to_plain_string (pp_value cval)
let string_of_pexpr pe =
  Pp_utils.to_plain_string (pp_pexpr pe)
let string_of_expr e =
  Pp_utils.to_plain_string (pp_expr e)
let string_of_file f =
  Pp_utils.to_plain_string (pp_file true f)


let string_of_params z =
  Pp_utils.to_plain_string (pp_params z)
(* let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def) *)

let mk_string_of_continuation_element = function
  | Kunseq (es1, es2) ->
      fun z ->
        let str1 = List.fold_right (fun e acc -> string_of_expr e ^ " || " ^ acc) es1 "" in
        let str2 = List.fold_right (fun e acc -> acc ^ "|| " ^ string_of_expr e) es2 "" in
        "[ " ^ str1 ^ z ^ str2 ^ " ]"
  | Kwseq (_as, e) ->
      fun z ->
        let str = string_of_expr e in
        "let weak TODO = " ^ z ^ " in " ^ str
  | Ksseq (_as, e) ->
      fun z ->
        let str = string_of_expr e in
        "let strong TODO = " ^ z ^ " in " ^ str

let string_of_continuation cont =
  List.fold_left (fun acc cont_elem -> mk_string_of_continuation_element cont_elem acc) "[]" cont


let rec string_of_stack sk =
  Pp_utils.to_plain_string (pp_stack sk)
