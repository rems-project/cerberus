open Datatypes

type 'a coq_Stream = 'a __coq_Stream Lazy.t
and 'a __coq_Stream =
| Cons of 'a * 'a coq_Stream

(** val hd : 'a1 coq_Stream -> 'a1 **)

let hd x =
  let Cons (a, s) = Lazy.force x in a

(** val tl : 'a1 coq_Stream -> 'a1 coq_Stream **)

let tl x =
  let Cons (a, s) = Lazy.force x in s

(** val coq_Str_nth_tl : nat -> 'a1 coq_Stream -> 'a1 coq_Stream **)

let rec coq_Str_nth_tl n s =
  match n with
  | O -> s
  | S m -> coq_Str_nth_tl m (tl s)

(** val coq_Str_nth : nat -> 'a1 coq_Stream -> 'a1 **)

let coq_Str_nth n s =
  hd (coq_Str_nth_tl n s)

(** val map : ('a1 -> 'a2) -> 'a1 coq_Stream -> 'a2 coq_Stream **)

let rec map f s =
  lazy (Cons ((f (hd s)), (map f (tl s))))

(** val const : 'a1 -> 'a1 coq_Stream **)

let rec const a =
  lazy (Cons (a, (const a)))

(** val zipWith :
    ('a1 -> 'a2 -> 'a3) -> 'a1 coq_Stream -> 'a2 coq_Stream -> 'a3 coq_Stream **)

let rec zipWith f a b =
  lazy (Cons ((f (hd a) (hd b)), (zipWith f (tl a) (tl b))))

