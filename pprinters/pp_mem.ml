open Mem
open Mem_common

open Pp_prelude

module Impl = Pp_defacto_memory


let pp_pure_memop = function
  | PURE_MEMOP_TODO ->
      !^ "PURE_MEMOP_TODO"

let pp_memop = function
  | PtrEq ->
      !^ "\"ptreq\""
  | PtrNe ->
      !^ "\"ptrne\""
  | PtrLt ->
      !^ "\"ptrlt\""
  | PtrGt ->
      !^ "\"ptrgt\""
  | PtrLe ->
      !^ "\"ptrle\""
  | PtrGe ->
      !^ "\"ptrge\""
  | Ptrdiff ->
      !^ "\"ptrdiff\""
  | IntFromPtr ->
      !^ "\"intfromptr\""
  | PtrFromInt ->
      !^ "\"ptrfromint\""
  | PtrValidForDeref ->
      !^ "\"ptrvalidforderef\""


(* let pp_pointer_shift = Impl.pp_pointer_shift *)
let pp_pointer_value = Impl.pp_pointer_value
let pp_integer_value = Impl.pp_integer_value
let pp_integer_value_for_core = Impl.pp_integer_value_for_core
let pp_mem_value = Impl.pp_mem_value
let pp_pretty_pointer_value = Impl.pp_pretty_pointer_value
let pp_pretty_mem_value = Impl.pp_pretty_mem_value
