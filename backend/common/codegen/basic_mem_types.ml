open Core_ctype
open AilTypes
open Nat_big_num
open Mem_common

exception Error of string

type impl_mem_value =
  | Integer of (integerType * num option)
  | Pointer of (ctype0 * num option)
  | Array of impl_mem_value list
  | Struct of Symbol.sym * (Cabs.cabs_identifier * impl_mem_value) list
  | Union of Symbol.sym * Cabs.cabs_identifier * impl_mem_value

type impl_integer_value = (integerType * num option)
type impl_pointer_value = (ctype0 * num option)
type impl_floating_value = unit (* not supported *)
type impl_footprint = unit (* not supported *)
type mem_constraint = unit
type shift_path = unit