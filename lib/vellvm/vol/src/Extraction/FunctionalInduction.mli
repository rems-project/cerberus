type __ = Obj.t

type 'a coq_FunctionalInduction =
  | Build_FunctionalInduction

val coq_FunctionalInduction_rect :
  'a1 -> (__ -> __ -> 'a2) -> 'a1 coq_FunctionalInduction -> 'a2

val coq_FunctionalInduction_rec :
  'a1 -> (__ -> __ -> 'a2) -> 'a1 coq_FunctionalInduction -> 'a2

