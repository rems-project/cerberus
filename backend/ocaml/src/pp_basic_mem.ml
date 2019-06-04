open Util
open Nat_big_num
open Pp_prelude
open Basic_mem

let print_opt_num (_,n) = !^(Option.case to_string (fun _ -> "Unspecified") n)
let pp_pointer_value = print_opt_num
let pp_integer_value = print_opt_num
let pp_integer_value_for_core = print_opt_num
let pp_mem_value mv = !^(impl_prettyStringFromMem_value mv)
let pp_pretty_pointer_value = print_opt_num
let pp_pretty_integer_value _ = print_opt_num
let pp_pretty_mem_value _ = pp_mem_value
