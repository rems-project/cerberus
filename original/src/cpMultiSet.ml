module M = BatMap

type 'a t = ('a, int) M.t

let empty = M.empty

let find x mset =
  try
    M.find x mset
  with
    Not_found -> 0

let add x mset =
  let count = find x mset in
  M.add x (count + 1) mset

let compare m1 m2 = M.compare compare m1 m2

let from_list ls = List.fold_left (fun mset x -> add x mset) empty ls
