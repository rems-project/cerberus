open Datatypes

type 'a coq_Stream = 'a __coq_Stream Lazy.t
and 'a __coq_Stream =
| Cons of 'a * 'a coq_Stream

val hd : 'a1 coq_Stream -> 'a1

val tl : 'a1 coq_Stream -> 'a1 coq_Stream

val coq_Str_nth_tl : nat -> 'a1 coq_Stream -> 'a1 coq_Stream

val coq_Str_nth : nat -> 'a1 coq_Stream -> 'a1

val map : ('a1 -> 'a2) -> 'a1 coq_Stream -> 'a2 coq_Stream

val const : 'a1 -> 'a1 coq_Stream

val zipWith :
  ('a1 -> 'a2 -> 'a3) -> 'a1 coq_Stream -> 'a2 coq_Stream -> 'a3 coq_Stream

