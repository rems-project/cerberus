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

  | ME_eff_array_shift_ptrval (ptrval, cty, ival, res_ptrval) ->
    !^ "array_shift" ^^^ P.parens (pp_pointer_value ptrval)
                     ^^^ P.parens (pp_ctype cty)
                     ^^^ P.parens (pp_integer_value ival)
                     ^^^ P.parens (pp_pointer_value res_ptrval)

  | ME_eff_member_shift_ptrval (tag_sym, membr_ident, ptrval, res_ptrval) ->
    !^ "member_shift" ^^^ P.parens (pp_symbol tag_sym)
                      ^^^ P.parens (Pp_symbol.pp_identifier membr_ident)
                      ^^^ P.parens (pp_pointer_value ptrval)
                      ^^^ P.parens (pp_pointer_value res_ptrval)

let pp_trace evs =
  P.flow P.hardline (List.map pp_trace_event evs)

