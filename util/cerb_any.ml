let () = Random.self_init ()

(* NOTE: Ocaml random only works on the int64 range *)
let bounded_integer min max =
  let min64 = Z.to_int64 min in
  let max64 = Z.to_int64 max in
  let delta = Random.int64 @@ Int64.succ @@ Int64.sub max64 min64 in
  Z.of_int64 @@ Int64.add min64 delta

