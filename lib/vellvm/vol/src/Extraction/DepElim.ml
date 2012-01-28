open EqDec

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val block : 'a1 -> 'a1 **)

let block a =
  a

type 'a coq_NoConfusionPackage =
  __ -> 'a -> 'a -> __ -> __
  (* singleton inductive, whose constructor was Build_NoConfusionPackage *)

(** val coq_NoConfusionPackage_rect :
    (__ -> (__ -> 'a1 -> 'a1 -> __ -> __) -> 'a2) -> 'a1
    coq_NoConfusionPackage -> 'a2 **)

let coq_NoConfusionPackage_rect f n =
  f __ n

(** val coq_NoConfusionPackage_rec :
    (__ -> (__ -> 'a1 -> 'a1 -> __ -> __) -> 'a2) -> 'a1
    coq_NoConfusionPackage -> 'a2 **)

let coq_NoConfusionPackage_rec f n =
  f __ n

type ('a, 'x) coq_NoConfusion = __

(** val noConfusion :
    'a1 coq_NoConfusionPackage -> 'a1 -> 'a1 -> ('a1, 'a2) coq_NoConfusion **)

let noConfusion noConfusionPackage a b =
  noConfusionPackage __ a b __

type 'a coq_DependentEliminationPackage =
  __
  (* singleton inductive, whose constructor was Build_DependentEliminationPackage *)

(** val coq_DependentEliminationPackage_rect :
    (__ -> __ -> 'a2) -> 'a1 coq_DependentEliminationPackage -> 'a2 **)

let coq_DependentEliminationPackage_rect f d =
  f __ d

(** val coq_DependentEliminationPackage_rec :
    (__ -> __ -> 'a2) -> 'a1 coq_DependentEliminationPackage -> 'a2 **)

let coq_DependentEliminationPackage_rec f d =
  f __ d

type 'a elim_type = __

(** val elim : 'a1 coq_DependentEliminationPackage -> 'a1 elim_type **)

let elim dependentEliminationPackage =
  dependentEliminationPackage

(** val solution_left : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_left t x x0 =
  x

(** val solution_right : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_right t x x0 =
  x

(** val solution_left_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let solution_left_let b t x =
  x __

(** val solution_right_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let solution_right_let b t x =
  x __

(** val deletion : 'a1 -> 'a2 -> 'a2 **)

let deletion t x =
  x

(** val simplification_heq : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let simplification_heq x y x0 =
  x0 __

(** val simplification_existT2 : 'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3 **)

let simplification_existT2 p x y x0 =
  x0 __

(** val simplification_existT2_dec :
    'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3 **)

let simplification_existT2_dec h p x y x0 =
  x0 __

(** val simplification_existT1 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let simplification_existT1 p q x y x0 =
  x0 __ __

(** val simplification_K : 'a1 -> 'a2 -> 'a2 **)

let simplification_K x x0 =
  x0

(** val simplification_K_dec : 'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2 **)

let simplification_K_dec h x x0 =
  coq_K_dec h x x0

(** val inaccessible_pattern : 'a1 -> 'a1 **)

let inaccessible_pattern t =
  t

(** val hide_pattern : 'a1 -> 'a1 **)

let hide_pattern t =
  t

type ('b, 'a) add_pattern = 'a

type end_of_section = __end_of_section Lazy.t
and __end_of_section =
  | Coq_the_end_of_the_section

type 'a coq_ImpossibleCall = __

(** val elim_impossible_call : 'a1 -> 'a2 **)

let elim_impossible_call a =
  assert false (* absurd case *)

