open Pp_ail

let string_of_integerType_raw ity =
  Pp_utils.to_plain_string (pp_integerType_raw ity)

let string_of_ctype ty =
  Pp_utils.to_plain_string (pp_ctype ty)

let string_of_expr e =
  Pp_utils.to_plain_string (pp_expression e)

let string_of_qualifiers_human qs =
  Pp_utils.to_plain_string (pp_qualifiers_human qs)


(* DEBUG*)
let string_of_genTypeCategory gtc =
  Pp_utils.to_plain_string (pp_genTypeCategory gtc)

let string_of_ctype_raw ty =
  Pp_utils.to_plain_string (pp_ctype_raw ty)
