(** val prefix_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec prefix_dec h l1 l2 =
  match l1 with
    | [] -> true
    | y::l ->
        (match l2 with
           | [] -> false
           | a0::l3 ->
               let s = h y a0 in if s then prefix_dec h l l3 else false)

