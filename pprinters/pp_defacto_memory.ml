open Defacto_memory_types
open Pp_prelude

(* Use this to pprint things not yet recognised by the Core parser *)
let nonvalid =
  P.enclose (!^ "{#") (!^ "#}")


let string_of_integer_operator = function
  | Mem_common.IntAdd ->
      "+"
  | Mem_common.IntSub ->
      "-"
  | Mem_common.IntMul ->
      "*"
  | Mem_common.IntDiv ->
      "/"
  | Mem_common.IntMod ->
      "mod"
  | Mem_common.IntExp ->
      "^"



let pp_provenance_id prov_id =
  !^ (string_of_int prov_id)

let pp_allocation_id alloc_id =
  !^ (string_of_int alloc_id)


let pp_provenance = function
  | Prov_wildcard ->
      !^ "Prov_wildcard"
  | Prov_none ->
      !^ "Prov_none"
  | Prov_device ->
      !^ "Prov_device"
  | Prov_some ids ->
      !^ "Prov_some" ^^ P.braces (comma_list pp_provenance_id (Pset.elements ids))


let rec pp_pointer_value (PV (prov, ptr_val_, sh)) =
  !^ "PV" ^^ P.parens (pp_provenance prov ^^ P.comma ^^^ pp_pointer_value_base ptr_val_ ^^ P.comma ^^^ pp_shift_path sh)

and pp_pointer_value_base = function
  | PVnull ty ->
      !^ "PVnull" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
  | PVfunction sym ->
      !^ "PVfunction" ^^ P.parens (P.parens (!^ (Pp_symbol.to_string_pretty sym)))
  | PVbase (alloc_id, pref) ->
      !^ "PVbase" ^^ P.parens (pp_allocation_id alloc_id ^^ P.comma ^^^ Pp_symbol.pp_prefix pref)
  | PVfromint ival_ ->
      !^ "PVfromint" ^^ P.parens (pp_integer_value_base ival_)

and pp_shift_path_element = function
  | SPE_array (ty, ival_) ->
      !^ "SPE_array" ^^ P.parens (Pp_core_ctype.pp_ctype ty ^^ P.comma ^^ pp_integer_value_base ival_)
  | SPE_member (tag_sym, (Cabs.CabsIdentifier (_, memb_str))) ->
      !^ "SPE_post_padding" ^^ P.parens (!^ (Pp_symbol.to_string_pretty tag_sym) ^^ P.comma ^^^ !^ memb_str)
 
and pp_shift_path sh =
  P.brackets (comma_list pp_shift_path_element sh)


and pp_integer_value_base = function
  | IVconcrete n ->
      !^ "IVconcrete" ^^ P.parens (!^ (Nat_big_num.to_string n))
  | IVaddress n ->
      !^ "IVaddress" ^^ P.parens (!^ (string_of_int n))
  | IVfromptr (ty, ptr_val_) ->
      !^ "IVfromptr" ^^ P.parens (Pp_core_ctype.pp_ctype ty ^^ P.comma ^^^ pp_pointer_value_base ptr_val_)
  | IVop (iop, ival_s) ->
      !^ "IVop" ^^ P.parens (!^ (string_of_integer_operator iop) ^^ P.comma ^^^ comma_list pp_integer_value_base ival_s)
  | IVmax ity ->
      !^ "IVmax" ^^ P.parens (Pp_ail.pp_integerType ity)
  | IVmin ity ->
      !^ "IVmin" ^^ P.parens (Pp_ail.pp_integerType ity)
  | IVsizeof ty ->
      !^ "IVsizeof" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
  | IVoffsetof (tag_sym, Cabs.CabsIdentifier (_, memb_str)) ->
      !^ "IVoffset" ^^ P.parens (!^ (Pp_symbol.to_string_pretty tag_sym) ^^ P.comma ^^^ !^ memb_str)
  | IVptrdiff (ptr_val_1, ptr_val_2) ->
      !^ "IVptrdiff" ^^ P.parens (pp_pointer_value_base ptr_val_1 ^^ P.comma ^^^ pp_pointer_value_base ptr_val_2)
  | IVbyteof (ival_, mval) ->
      !^ "IVbyteof" ^^ P.parens (pp_integer_value_base ival_ ^^ P.comma ^^^ pp_mem_value mval)



and pp_integer_value (IV (prov, ival_)) =
  !^ "IV" ^^ P.parens (pp_provenance prov ^^ P.comma ^^^ pp_integer_value_base ival_)

and pp_mem_value = function
  | MVsymbolic symb ->
      !^ "MVsymbolic(TODO)"
  | MVunspecified ty ->
      !^ "MVunspecified" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
  | MVinteger (ity, ival) ->
      !^ "MVinteger" ^^ P.parens (Pp_ail.pp_integerType_raw ity ^^ P.comma ^^^ pp_integer_value ival)
  | MVfloating (fty, str) ->
      !^ ("MVfloating(TODO, " ^ str ^ ")")
  | MVpointer (ty, ptr_val) ->
      !^ "MVpointer" ^^ P.parens (Pp_core_ctype.pp_ctype ty ^^ P.comma ^^^ pp_pointer_value ptr_val)
  | MVarray mem_vals ->
      !^ "MVarray" ^^ P.parens (comma_list pp_mem_value mem_vals)
| MVstruct (tag_sym, xs) ->
      P.parens (
        !^ "struct" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)
     ) ^^^
     P.braces (
      comma_list (fun (mb_ident, mval) ->
        P.dot ^^ Pp_cabs.pp_cabs_identifier mb_ident ^^ P.equals ^^^ pp_mem_value mval
      ) xs
     )
  | MVunion (tag_sym, mb_ident, mval) ->
      P.parens (
        !^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)
      ) ^^^
      P.braces (
        P.dot ^^ Pp_cabs.pp_cabs_identifier mb_ident ^^ P.equals ^^^ pp_mem_value mval
      )


let pp_mem_constraint = function
  | MC_eqIV (debug_str, ival_1, ival_2) ->
      !^ "MC_eqIV" ^^ P.parens (P.dquotes (!^ debug_str) ^^ P.comma ^^^
                                pp_integer_value_base ival_1 ^^ P.comma ^^^
                                pp_integer_value_base ival_2)
  | MC_neIV (ival_1, ival_2) ->
      !^ "MC_neIV" ^^ P.parens (pp_integer_value_base ival_1 ^^ P.comma ^^^
                                pp_integer_value_base ival_2)
  | MC_leIV (ival_1, ival_2) ->
      !^ "MC_leIV" ^^ P.parens (pp_integer_value_base ival_1 ^^ P.comma ^^^
                                pp_integer_value_base ival_2)
  | MC_addr_distinct (addr_id, addr_ids) ->
      !^ "MC_addr_distinct(TODO)"
