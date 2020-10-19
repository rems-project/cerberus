include Nat_big_num

type t = num

let pp n = PPrint.(!^)(to_string n)

