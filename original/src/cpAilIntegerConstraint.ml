open CpPervasives

module AC = CpAilConstraint
module M = CpRange

let char_bit   = AC.fresh_named "char_bit"

(* Minimum and maximum  values. *)
let char_min   = AC.fresh_named "char_min"
let char_max   = AC.fresh_named "char_max"
let schar_min  = AC.fresh_named "schar_min"
let schar_max  = AC.fresh_named "schar_max"
let uchar_max  = AC.fresh_named "uchar_max"
let shrt_min   = AC.fresh_named "shrt_min"
let shrt_max   = AC.fresh_named "shrt_max"
let ushrt_max  = AC.fresh_named "ushrt_max"
let int_min    = AC.fresh_named "int_min"
let int_max    = AC.fresh_named "int_max"
let uint_max   = AC.fresh_named "uint_max"
let long_min   = AC.fresh_named "long_min"
let long_max   = AC.fresh_named "long_max"
let ulong_max  = AC.fresh_named "ulong_max"
let llong_min  = AC.fresh_named "llong_min"
let llong_max  = AC.fresh_named "llong_max"
let ullong_max = AC.fresh_named "ullong_max"

(* Byte sizes. *)
let bool_size   = AC.fresh_named "bool_size"
let char_size   = AC.fresh_named "char_size"
let schar_size  = AC.fresh_named "schar_size"
let uchar_size  = AC.fresh_named "uchar_size"
let char_size   = AC.fresh_named "char_size"
let shrt_size   = AC.fresh_named "shrt_size"
let ushrt_size  = AC.fresh_named "ushrt_size"
let int_size    = AC.fresh_named "int_size"
let uint_size   = AC.fresh_named "uint_size"
let long_size   = AC.fresh_named "long_size"
let ulong_size  = AC.fresh_named "ulong_size"
let llong_size  = AC.fresh_named "llong_size"
let ullong_size = AC.fresh_named "ullong_size"

(* Alignment requirements. *)
let bool_align   = AC.fresh_named "bool_align"
let char_align   = AC.fresh_named "char_align"
let schar_align  = AC.fresh_named "schar_align"
let uchar_align  = AC.fresh_named "uchar_align"
let char_align   = AC.fresh_named "char_align"
let shrt_align   = AC.fresh_named "shrt_align"
let ushrt_align  = AC.fresh_named "ushrt_align"
let int_align    = AC.fresh_named "int_align"
let uint_align   = AC.fresh_named "uint_align"
let long_align   = AC.fresh_named "long_align"
let ulong_align  = AC.fresh_named "ulong_align"
let llong_align  = AC.fresh_named "llong_align"
let ullong_align = AC.fresh_named "ullong_align"

let set = AC.from_list [
  AC.eq char_bit   (AC.const (M.char_bit));

  AC.le schar_min  (AC.const (M.min M.schar));
  AC.ge schar_max  (AC.const (M.max M.schar));
  AC.ge uchar_max  (AC.const (M.max M.uchar));
  AC.le shrt_min   (AC.const (M.min M.shrt));
  AC.ge shrt_max   (AC.const (M.max M.shrt));
  AC.ge ushrt_max  (AC.const (M.max M.ushrt));
  AC.le int_min    (AC.const (M.min M.int));
  AC.ge int_max    (AC.const (M.max M.int));
  AC.ge uint_max   (AC.const (M.max M.uint));
  AC.le long_min   (AC.const (M.min M.long));
  AC.ge long_max   (AC.const (M.max M.long));
  AC.ge ulong_max  (AC.const (M.max M.ulong));
  AC.le llong_min  (AC.const (M.min M.llong));
  AC.ge llong_max  (AC.const (M.max M.llong));
  AC.ge ullong_max (AC.const (M.max M.ullong));
]
