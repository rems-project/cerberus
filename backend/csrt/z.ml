include Big_int_Z

type t = Big_int_Z.big_int

let of_string = big_int_of_string

let of_int = big_int_of_int

let equal = eq_big_int

let zero = zero_big_int

let sub = sub_big_int

let compare = compare_big_int

let pp n = 
  PPrint.(!^)(string_of_big_int n)

let pp_hex length n = 
  let open Cerb_frontend.String_nat_big_num in
  let open Pp in
  !^(string_of_hexadecimal_pad length n)
