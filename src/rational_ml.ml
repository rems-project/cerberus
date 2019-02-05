(* rational.ml - rational numbers *)
(* (C) J Pichon 2019 *)

let rec gcd a b = if b = 0 then a else gcd b (a mod b)

type t = int * int

let simplify (n, d) =
  let n = n * (d / abs d) in
  let d = abs d in
  let g = abs (gcd n d) in
  (n / g, d / g)

let compare (x : t) y =
  let (n1, d1) = simplify x in
  let (n2, d2) = simplify y in
  Pervasives.compare (n1 * d2) (n2 * d1)

let max (n1, d1) (n2, d2) =
  if n1 * d2 < d1 * n2 then (n2, d2) else (n1, d1)

let min (n1, d1) (n2, d2) =
  if n1 * d2 < d1 * n2 then (n1, d1) else (n2, d2)

let add (n1, d1) (n2, d2) =
  simplify (n1 * d2 + d1 * n2, d1 * d2)

let addn rs =
  List.fold_left
    add
    (0, 1)
    rs

let sub x (n2, d2) =
  add x (- n2, d2)

let mult (n1, d1) (n2, d2) =
  simplify (n1 * n2, d1 * d2)

let div (n1, d1) (n2, d2) =
  simplify (n1 * d2, d1 * n2)

let div_int (n, d) k = simplify (n, d * k)

let string_of (n, d) =
  string_of_int n ^ "/" ^ string_of_int d

let float_of (n, d) =
  float_of_int n /. float_of_int d