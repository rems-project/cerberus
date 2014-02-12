type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val unit_rect : 'a1 -> unit -> 'a1 **)

let unit_rect f u =
  f

(** val unit_rec : 'a1 -> unit -> 'a1 **)

let unit_rec f u =
  f

(** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rect f f0 = function
| true -> f
| false -> f0

(** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rec f f0 = function
| true -> f
| false -> f0

(** val andb : bool -> bool -> bool **)

let andb b1 b2 =
  if b1 then b2 else false

(** val orb : bool -> bool -> bool **)

let orb b1 b2 =
  if b1 then true else b2

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  if b1 then b2 else true

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val eq_true_rect : 'a1 -> bool -> 'a1 **)

let eq_true_rect f b =
  f

(** val eq_true_rec : 'a1 -> bool -> 'a1 **)

let eq_true_rec f b =
  f

(** val eq_true_rec_r : bool -> 'a1 -> 'a1 **)

let eq_true_rec_r b h =
  h

(** val eq_true_rect_r : bool -> 'a1 -> 'a1 **)

let eq_true_rect_r b h =
  h

type nat =
| O
| S of nat

(** val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

let rec nat_rect f f0 = function
| O -> f
| S n0 -> f0 n0 (nat_rect f f0 n0)

(** val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

let rec nat_rec f f0 = function
| O -> f
| S n0 -> f0 n0 (nat_rec f f0 n0)

type coq_Empty_set = unit (* empty inductive *)

(** val coq_Empty_set_rect : coq_Empty_set -> 'a1 **)

let coq_Empty_set_rect e =
  assert false (* absurd case *)

(** val coq_Empty_set_rec : coq_Empty_set -> 'a1 **)

let coq_Empty_set_rec e =
  assert false (* absurd case *)

type 'a identity =
| Coq_identity_refl

(** val identity_rect : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let identity_rect a f y =
  f

(** val identity_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let identity_rec a f y =
  f

(** val option_rect : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let option_rect f f0 = function
| Some x -> f x
| None -> f0

(** val option_rec : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

let option_rec f f0 = function
| Some x -> f x
| None -> f0

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

(** val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rect f f0 = function
| Coq_inl x -> f x
| Coq_inr x -> f0 x

(** val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rec f f0 = function
| Coq_inl x -> f x
| Coq_inr x -> f0 x

(** val prod_rect : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3 **)

let prod_rect f = function
| x,x0 -> f x x0

(** val prod_rec : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3 **)

let prod_rec f = function
| x,x0 -> f x x0

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| x,y -> y

(** val prod_uncurry : (('a1*'a2) -> 'a3) -> 'a1 -> 'a2 -> 'a3 **)

let prod_uncurry f x y =
  f (x,y)

(** val prod_curry : ('a1 -> 'a2 -> 'a3) -> ('a1*'a2) -> 'a3 **)

let prod_curry f = function
| x,y -> f x y

type comparison =
| Eq
| Lt
| Gt

(** val comparison_rect : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rect f f0 f1 = function
| Eq -> f
| Lt -> f0
| Gt -> f1

(** val comparison_rec : 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rec f f0 f1 = function
| Eq -> f
| Lt -> f0
| Gt -> f1

(** val coq_CompOpp : comparison -> comparison **)

let coq_CompOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a coq_CompSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val coq_CompSpecT_rect :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> comparison ->
    'a1 coq_CompSpecT -> 'a2 **)

let coq_CompSpecT_rect x y f f0 f1 c = function
| CompEqT -> f __
| CompLtT -> f0 __
| CompGtT -> f1 __

(** val coq_CompSpecT_rec :
    'a1 -> 'a1 -> (__ -> 'a2) -> (__ -> 'a2) -> (__ -> 'a2) -> comparison ->
    'a1 coq_CompSpecT -> 'a2 **)

let coq_CompSpecT_rec x y f f0 f1 c = function
| CompEqT -> f __
| CompLtT -> f0 __
| CompGtT -> f1 __

(** val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT **)

let coq_CompSpec2Type x y = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type coq_ID = __ -> __ -> __

(** val id : 'a1 -> 'a1 **)

let id x =
  x

(** val list_rect :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec list_rect f f0 = function
| [] -> f
| y::l0 -> f0 y l0 (list_rect f f0 l0)

(** val list_rec :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec list_rec f f0 = function
| [] -> f
| y::l0 -> f0 y l0 (list_rec f f0 l0)

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| y::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

