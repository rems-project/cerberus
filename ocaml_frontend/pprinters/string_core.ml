(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2011-2020                                                         *)
(*    Kayvan Memarian                                                               *)
(*    Victor Gomes                                                                  *)
(*    Justus Matthiesen                                                             *)
(*    Peter Sewell                                                                  *)
(*    Kyndylan Nienhuis                                                             *)
(*    Stella Lau                                                                    *)
(*    Jean Pichon-Pharabod                                                          *)
(*    Christopher Pulte                                                             *)
(*    Rodolphe Lepigre                                                              *)
(*    James Lingard                                                                 *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(************************************************************************************)

open Core
open Pp_core.Basic

let string_of_core_object_type oTy =
  Pp_utils.to_plain_string (pp_core_object_type oTy)
let string_of_core_base_type bTy =
  Pp_utils.to_plain_string (pp_core_base_type bTy)
let string_of_value cval =
  Pp_utils.to_plain_string (pp_value cval)
let string_of_action act =
  Pp_utils.to_plain_string (pp_action act)
let string_of_pexpr pe =
  Pp_utils.to_plain_string (pp_pexpr pe)
let string_of_expr e =
  Pp_utils.to_plain_string (pp_expr e)
let string_of_file f =
  Pp_utils.to_plain_string (pp_file f)

let string_of_params z =
  Pp_utils.to_plain_string (pp_params z)
(* let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def) *)

let mk_string_of_continuation_element = function
  | Kunseq (_, es1, es2) ->
      fun z ->
        let str1 = List.fold_right (fun e acc -> string_of_expr e ^ " || " ^ acc) es1 "" in
        let str2 = List.fold_right (fun e acc -> acc ^ "|| " ^ string_of_expr e) es2 "" in
        "[ " ^ str1 ^ z ^ str2 ^ " ]"
  | Kwseq (_, _as, e) ->
      fun z ->
        let str = string_of_expr e in
        "let weak TODO = " ^ z ^ " in " ^ str
  | Ksseq (_, _as, e) ->
      fun z ->
        let str = string_of_expr e in
        "let strong TODO = " ^ z ^ " in " ^ str

let string_of_continuation cont =
  List.fold_left (fun acc cont_elem -> mk_string_of_continuation_element cont_elem acc) "[]" cont


let rec string_of_stack sk =
  Pp_utils.to_plain_string (pp_stack sk)
