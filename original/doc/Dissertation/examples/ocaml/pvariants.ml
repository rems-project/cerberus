type num = [`Num of int ]
type add = [`Num of int | `Add of add * add]

let is_num = function
  | `Nu  _ -> true
  | _      -> false
