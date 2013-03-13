type __ = Obj.t

val unit_rect : 'a1 -> unit -> 'a1

val unit_rec : 'a1 -> unit -> 'a1

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

val andb : bool -> bool -> bool

val orb : bool -> bool -> bool

val implb : bool -> bool -> bool

val xorb : bool -> bool -> bool

val negb : bool -> bool

val eq_true_rect : 'a1 -> bool -> 'a1

val eq_true_rec : 'a1 -> bool -> 'a1

val eq_true_rec_r : bool -> 'a1 -> 'a1

val eq_true_rect_r : bool -> 'a1 -> 'a1

type nat =
| O
| S of nat

val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

type coq_Empty_set = unit (* empty inductive *)

val coq_Empty_set_rect : coq_Empty_set -> 'a1

val coq_Empty_set_rec : coq_Empty_set -> 'a1

type 'a identity =
| Coq_identity_refl

val identity_rect : 'a1 -> 'a2 -> 'a1 -> 'a2

val identity_rec : 'a1 -> 'a2 -> 'a1 -> 'a2

val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

type ('a, 'b) prod =
| Coq_pair of 'a * 'b

val prod_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

val prod_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

val prod_uncurry : (('a1, 'a2) prod -> 'a3) -> 'a1 -> 'a2 -> 'a3

val prod_curry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

type comparison =
| Eq
| Lt
| Gt

val comparison_rect : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val comparison_rec : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val coq_CompOpp : comparison -> comparison

type 'a coq_CompSpecT =
| CompEqT
| CompLtT
| CompGtT

val coq_CompSpecT_rect :
  'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> comparison ->
  'a1 coq_CompSpecT -> 'a2

val coq_CompSpecT_rec :
  'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> comparison ->
  'a1 coq_CompSpecT -> 'a2

val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT

type coq_ID = __ -> __ -> __

val id : 'a1 -> 'a1

val list_rect : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val list_rec : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

