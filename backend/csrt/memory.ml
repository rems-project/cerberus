module CF=Cerb_frontend
open PPrint
open Num
open Except
open TypeErrors
open BaseTypes




let integer_value_to_num loc iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc Integer_value_error

let size_of_ctype loc ct = 
  let s = CF.Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let size_of_struct_type loc (Tag s) =
  size_of_ctype loc (CF.Ctype.Ctype ([], CF.Ctype.Struct s))



type mcl_field = {ct: CF.Ctype.ctype; pstart: Num.t; pend: Num.t}
type mcl_fields = (member * mcl_field) list
type mcl_padding = {pstart: Num.t; pend: Num.t}
type mcl_paddings = mcl_padding list
type mcl = {fields: mcl_fields; paddings: mcl_paddings}

let struct_ct_and_layout file loc genv (Tag s) fields = 
  let rec aux acc_fields acc_padding position  = function
    | (id, (_attributes, _qualifier, ct)) :: fields ->
       let offset_ival = CF.Impl_mem.offsetof_ival file.CF.Mucore.mu_tagDefs s id in
       let* offset = integer_value_to_num Loc.unknown offset_ival in
       if Num.greater_equal offset position then
         let* size = size_of_ctype loc ct in
         let pstart = offset in
         let pend = Num.add offset size in
         let acc_fields = acc_fields@[(Member (Id.s id),{ct;pstart;pend})] in
         let acc_padding = 
           if Num.equal offset position 
           then acc_padding
           else acc_padding @ [{pstart=position; pend = Num.pred offset}]
         in
         aux acc_fields acc_padding (Num.succ pend) fields
       else
         fail loc (Unreachable !^"struct offset too small")
    | [] -> return (acc_fields, acc_padding)
  in
  let* (fields,paddings) = aux [] [] zero fields in
  return {fields;paddings}
  


let integer_value_min loc it = 
  integer_value_to_num loc (CF.Impl_mem.min_ival it)

let integer_value_max loc it = 
  integer_value_to_num loc (CF.Impl_mem.max_ival it)
