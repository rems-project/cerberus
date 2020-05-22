open PPrint
open Num
open Cerb_frontend
open Except
open TypeErrors
open BaseTypes




let integer_value_to_num loc iv = 
  match Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc Integer_value_error

let size_of_ctype loc ct = 
  let s = Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let size_of_struct_type loc (S_Id sym) =
  size_of_ctype loc (Ctype.Ctype ([], Ctype.Struct sym))



type mcl_field = {ct: Ctype.ctype; pstart: Num.t; pend: Num.t}
type mcl_fields = (string * mcl_field) list
type mcl_padding = {pstart: Num.t; pend: Num.t}
type mcl_paddings = mcl_padding list
type mcl = {fields: mcl_fields; paddings: mcl_paddings}

let struct_ct_and_layout file loc genv (S_Id typ) fields = 
  let rec aux acc_fields acc_padding position  = function
    | (id, (_attributes, _qualifier, ct)) :: fields ->
       let offset_ival = Impl_mem.offsetof_ival file.Mucore.mu_tagDefs typ id in
       integer_value_to_num Loc.unknown offset_ival >>= fun offset ->
       if Num.greater_equal offset position then
         size_of_ctype loc ct >>= fun size ->
         let pstart = offset in
         let pend = Num.add offset size in
         let acc_fields = acc_fields@[(Id.s id,{ct;pstart;pend})] in
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
  aux [] [] zero fields >>= fun (fields,paddings) ->
  return {fields;paddings}
  


let integer_value_min loc it = 
  integer_value_to_num loc (Impl_mem.min_ival it)

let integer_value_max loc it = 
  integer_value_to_num loc (Impl_mem.max_ival it)
