open Apron

type state = Box.t Abstract1.t

let man = Box.manager_alloc ()

let empty_env = Environment.make [||] [||]

(* Lift states to a common environment *)
let lift_common_env man (s1, s2) =
  let env1 = Abstract1.env s1 in
  let env2 = Abstract1.env s2 in
  match Environment.compare env1 env2 with
  | -2 -> (* incomparable environments *)
    assert false
  | -1 ->
    let s1 = Abstract1.change_environment man s1 env2 true
    in (s1, s2)
  | 0 -> (* equal *)
    (s1, s2)
  | 1 ->
    let s2 = Abstract1.change_environment man s2 env1 true
    in (s1, s2)
  | 2 -> (* it exists a common one *)
    let env = Environment.lce env1 env2 in
    let s1 = Abstract1.change_environment man s1 env true in
    let s2 = Abstract1.change_environment man s2 env true in
    (s1, s2)
  | n ->
    failwith ("lift_common_env: " ^ string_of_int n)

let leq s1 s2 =
  let (s1, s2) = lift_common_env man (s1, s2) in
  Abstract1.is_leq man s1 s2

let join man s1 s2 =
  let (s1, s2) = lift_common_env man (s1, s2) in
  Abstract1.join man s1 s2

let widening man s1 s2 =
  let (s1, s2) = lift_common_env man (s1, s2) in
  Abstract1.widening man s1 s2

let bot =
  Abstract1.bottom man empty_env

let top =
  Abstract1.top man empty_env


