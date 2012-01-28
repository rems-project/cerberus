type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_FunctionalInduction =
  | Build_FunctionalInduction

(** val coq_FunctionalInduction_rect :
    'a1 -> (__ -> __ -> 'a2) -> 'a1 coq_FunctionalInduction -> 'a2 **)

let coq_FunctionalInduction_rect f f0 f1 =
  f0 __ __

(** val coq_FunctionalInduction_rec :
    'a1 -> (__ -> __ -> 'a2) -> 'a1 coq_FunctionalInduction -> 'a2 **)

let coq_FunctionalInduction_rec f f0 f1 =
  f0 __ __

