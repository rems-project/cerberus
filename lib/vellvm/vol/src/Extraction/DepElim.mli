open EqDec

type __ = Obj.t

val block : 'a1 -> 'a1

type 'a coq_NoConfusionPackage =
  __ -> 'a -> 'a -> __ -> __
  (* singleton inductive, whose constructor was Build_NoConfusionPackage *)

val coq_NoConfusionPackage_rect :
  (__ -> (__ -> 'a1 -> 'a1 -> __ -> __) -> 'a2) -> 'a1 coq_NoConfusionPackage
  -> 'a2

val coq_NoConfusionPackage_rec :
  (__ -> (__ -> 'a1 -> 'a1 -> __ -> __) -> 'a2) -> 'a1 coq_NoConfusionPackage
  -> 'a2

type ('a, 'x) coq_NoConfusion = __

val noConfusion :
  'a1 coq_NoConfusionPackage -> 'a1 -> 'a1 -> ('a1, 'a2) coq_NoConfusion

type 'a coq_DependentEliminationPackage =
  __
  (* singleton inductive, whose constructor was Build_DependentEliminationPackage *)

val coq_DependentEliminationPackage_rect :
  (__ -> __ -> 'a2) -> 'a1 coq_DependentEliminationPackage -> 'a2

val coq_DependentEliminationPackage_rec :
  (__ -> __ -> 'a2) -> 'a1 coq_DependentEliminationPackage -> 'a2

type 'a elim_type = __

val elim : 'a1 coq_DependentEliminationPackage -> 'a1 elim_type

val solution_left : 'a1 -> 'a2 -> 'a1 -> 'a2

val solution_right : 'a1 -> 'a2 -> 'a1 -> 'a2

val solution_left_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val solution_right_let : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val deletion : 'a1 -> 'a2 -> 'a2

val simplification_heq : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val simplification_existT2 : 'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3

val simplification_existT2_dec :
  'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2 -> (__ -> 'a3) -> 'a3

val simplification_existT1 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val simplification_K : 'a1 -> 'a2 -> 'a2

val simplification_K_dec : 'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2

val inaccessible_pattern : 'a1 -> 'a1

val hide_pattern : 'a1 -> 'a1

type ('b, 'a) add_pattern = 'a

type end_of_section = __end_of_section Lazy.t
and __end_of_section =
  | Coq_the_end_of_the_section

type 'a coq_ImpossibleCall = __

val elim_impossible_call : 'a1 -> 'a2

