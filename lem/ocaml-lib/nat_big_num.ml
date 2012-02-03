module BI = Big_int

type num = BI.big_int
let (<) = BI.lt_big_int
let (<=) = BI.le_big_int
let (>) = BI.gt_big_int
let (>=) = BI.ge_big_int
let (+) = BI.add_big_int
let (-) x y =
  let d = BI.sub_big_int x y in
    if d < BI.zero_big_int then
      BI.zero_big_int
    else
      d
let ( * ) = BI.mult_big_int
let (/) = BI.div_big_int
let string_of_num = BI.string_of_big_int
let compare_num x y = BI.big_int_of_int (compare x y)
let (%) n m = BI.mod_big_int n m

let ( ** ) = BI.power_big_int_positive_big_int
