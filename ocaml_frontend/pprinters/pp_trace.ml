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

open Colour
open Pp_prelude
open Trace_event
open Impl_mem
open Pp_symbol
open Pp_core_ctype


let pp_symbol  a = !^ (ansi_format [Blue] (to_string_pretty a))

let pp_mem_value_opt = function
  | Some mval -> pp_mem_value mval
  | None -> P.empty

let pp_string_opt = function
    | None -> P.empty
    | Some s -> !^s

let pp_trace_event = function
  | ME_function_call (f, mvs) ->
    !^ "function_call" ^^^ pp_symbol f
                       ^^^ P.parens (comma_list pp_mem_value mvs)

  | ME_function_return (f, mval_opt) ->
    !^ "function_return" ^^^ pp_symbol f
                         ^^^ P.parens (pp_mem_value_opt mval_opt)

  | ME_allocate_object (tid, pre, align_ival, cty, mval_opt, ptrval) ->
    !^ "allocate_object" ^^^ !^(string_of_int tid)
                         ^^^ P.parens (pp_prefix pre)
                         ^^^ P.parens (pp_integer_value align_ival)
                         ^^^ P.parens (pp_ctype cty)
                         ^^^ P.parens (pp_mem_value_opt mval_opt)
                         ^^^ P.parens (pp_pointer_value ptrval)

  | ME_allocate_region (tid, pre, align_ival, size_ival, ptrval) ->
    !^ "allocate_region" ^^^ !^(string_of_int tid)
                         ^^^ P.parens (pp_prefix pre)
                         ^^^ P.parens (pp_integer_value align_ival)
                         ^^^ P.parens (pp_integer_value size_ival)
                         ^^^ P.parens (pp_pointer_value ptrval)

  | ME_kill (loc, is_dyn, ptrval) ->
    !^ "kill" ^^^ P.parens !^(Location_ocaml.location_to_string loc)
              ^^^ !^(string_of_bool is_dyn)
              ^^^ pp_pointer_value ptrval

  | ME_load (loc, pref, cty, ptrval, mval) ->
    !^ "load" ^^^ P.parens !^(Location_ocaml.location_to_string loc)
              ^^^ P.parens (pp_string_opt pref)
              ^^^ P.parens (pp_ctype cty)
              ^^^ P.parens (pp_pointer_value ptrval)
              ^^^ P.parens (pp_mem_value mval)

  | ME_store (loc, pref, cty, is_locking, ptrval, mval) ->
    !^ "store" ^^^ P.parens !^(Location_ocaml.location_to_string loc)
               ^^^ P.parens (pp_string_opt pref)
               ^^^ P.parens (pp_ctype cty)
               ^^^ !^(string_of_bool is_locking)
               ^^^ P.parens (pp_pointer_value ptrval)
               ^^^ P.parens (pp_mem_value mval)

  | ME_eff_array_shift_ptrval (arr_ptrval, cty, ival, ptrval) ->
    !^ "array_shift (TODO)"

  | ME_member_shift _ ->
    !^ "member_shift (TODO)"

let pp_trace evs =
  P.flow P.hardline (List.map pp_trace_event evs)

