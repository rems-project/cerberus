open Pp_ail

let string_of_integerType ity =
  Pp_utils.to_plain_string (Pp_ail.pp_integerType ity)

let string_of_integerType_raw ity =
  Pp_utils.to_plain_string (Pp_ail_raw.pp_integerType_raw ity)

let string_of_ctype qs ty =
  Pp_utils.to_plain_string (pp_ctype qs ty)

let string_of_expression e =
  Pp_utils.to_plain_string (pp_expression e)

let string_of_qualifiers_human qs =
  Pp_utils.to_plain_string (pp_qualifiers_human qs)


(* DEBUG*)
let string_of_genType gty =
  Pp_utils.to_plain_string (pp_genType gty)

let string_of_genTypeCategory gtc =
  Pp_utils.to_plain_string (pp_genTypeCategory gtc)

let string_of_ctype_raw ty =
  Pp_utils.to_plain_string (Pp_ail_raw.pp_ctype_raw ty)

let string_of_ctype_human qs ty =
  Pp_utils.to_plain_string (Pp_ail.pp_ctype_human qs ty)
