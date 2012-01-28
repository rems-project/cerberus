open List0

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
  | [] -> a::[]
  | a1::x1 -> if aeq_dec a a1 then a1::x1 else a1::(set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
  | [] -> false
  | a1::x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_remove aeq_dec a = function
  | [] -> empty_set
  | a1::x1 -> if aeq_dec a a1 then x1 else a1::(set_remove aeq_dec a x1)

(** val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x y =
  match x with
    | [] -> []
    | a1::x1 ->
        if set_mem aeq_dec a1 y
        then a1::(set_inter aeq_dec x1 y)
        else set_inter aeq_dec x1 y

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
  | [] -> x
  | a1::y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

(** val set_diff : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_diff aeq_dec x y =
  match x with
    | [] -> []
    | a1::x1 ->
        if set_mem aeq_dec a1 y
        then set_diff aeq_dec x1 y
        else set_add aeq_dec a1 (set_diff aeq_dec x1 y)

(** val set_In_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_In_dec aeq_dec a = function
  | [] -> false
  | y::l -> if aeq_dec a y then true else set_In_dec aeq_dec a l

(** val set_prod : 'a1 set -> 'a2 set -> ('a1*'a2) set **)

let set_prod x x0 =
  list_prod x x0

(** val set_power : 'a1 set -> 'a2 set -> ('a1*'a2) set set **)

let set_power x x0 =
  list_power x x0

(** val set_fold_left : ('a2 -> 'a1 -> 'a2) -> 'a1 set -> 'a2 -> 'a2 **)

let set_fold_left =
  fold_left

(** val set_fold_right : ('a1 -> 'a2 -> 'a2) -> 'a1 set -> 'a2 -> 'a2 **)

let set_fold_right f x b =
  fold_right f b x

(** val set_map :
    ('a2 -> 'a2 -> bool) -> ('a1 -> 'a2) -> 'a1 set -> 'a2 set **)

let set_map aeq_dec f x =
  set_fold_right (fun a -> set_add aeq_dec (f a)) x empty_set

