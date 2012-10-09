type num = int
let (<) = (<)
let (<=) = (<=)
let (>) = (>)
let (>=) = (>=)
let (+) = (+)
let (-) = (-)
let ( * ) = ( * )
let (/) = (/)
let (land) = (land)
let string_of_num n = string_of_int n

(* CSEM STUFF *)
let (%) n m = n mod m
let rec pow a n =
  match n with
    | 0 -> 1
    | 1 -> a
    | n ->
        let b = pow a (n/2) in
        b * b * (if n % 2 = 0 then 1 else a)
let ( ** ) = pow

let int_of_num n = n
let num_of_int n = n
let num_of_string s = int_of_string s

let compare_num x y = compare x y

