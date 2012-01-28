open Ensembles

type 'u coq_U_set = 'u coq_Ensemble

(** val coq_Union_dec : 'a1 -> bool -> bool -> bool **)

let coq_Union_dec x h h0 =
  if h then true else if h0 then false else assert false (* absurd case *)

