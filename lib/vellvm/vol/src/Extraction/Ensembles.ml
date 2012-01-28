type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'u coq_Ensemble = __

(** val coq_Empty_set_rect : 'a1 -> 'a2 **)

let coq_Empty_set_rect u =
  assert false (* absurd case *)

(** val coq_Empty_set_rec : 'a1 -> 'a2 **)

let coq_Empty_set_rec u =
  assert false (* absurd case *)

(** val coq_Singleton_rect : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let coq_Singleton_rect x f u =
  f

(** val coq_Singleton_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let coq_Singleton_rec x f u =
  f

(** val coq_Disjoint_rect : (__ -> 'a2) -> 'a2 **)

let coq_Disjoint_rect f =
  f __

(** val coq_Disjoint_rec : (__ -> 'a2) -> 'a2 **)

let coq_Disjoint_rec f =
  f __

