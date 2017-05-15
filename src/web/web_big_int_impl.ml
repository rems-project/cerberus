module BI = struct
  include Big_int
  let (mod) x y = raise (Failure "Big_int mod")
  let div x y  = raise (Failure "Big_int div")
end
