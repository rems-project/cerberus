let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str


let pp_ail_ctype ty = to_plain_string (Pp_ail.pp_ctype ty)
let pp_ail_expr e = to_plain_string (Pp_ail.pp_expression e)
let pp_core_expr e = to_plain_string (Pp_core.pp_expr e)
let pp_core_file f = to_plain_string (Pp_core.pp_file f)

let pp_core_params z = to_plain_string (Pp_core.pp_params z)
let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def)

