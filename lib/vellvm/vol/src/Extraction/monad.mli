open Compare_dec
open Datatypes
open Peano

type __ = Obj.t

val mbind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

val mif : bool -> 'a1 option -> 'a1 option -> 'a1 option

val mswitch : (bool*'a1 option) list -> 'a1 option -> 'a1 option

val mfor : 'a1 list -> ('a1 -> __ option) -> __ option

type coq_Range = { coq_Range_b : nat; coq_Range_e : nat; coq_Range_d : nat }

val coq_Range_rect : (nat -> nat -> nat -> __ -> 'a1) -> coq_Range -> 'a1

val coq_Range_rec : (nat -> nat -> nat -> __ -> 'a1) -> coq_Range -> 'a1

val coq_Range_b : coq_Range -> nat

val coq_Range_e : coq_Range -> nat

val coq_Range_d : coq_Range -> nat

val _range2list_F : (coq_Range -> nat list) -> coq_Range -> nat list

val _range2list_terminate : coq_Range -> nat list

val _range2list : coq_Range -> nat list

type coq_R__range2list =
  | R__range2list_0 of coq_Range * nat * nat * nat
  | R__range2list_1 of coq_Range * nat * nat * nat * 
     nat list * coq_R__range2list

val coq_R__range2list_rect :
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> nat list ->
  coq_R__range2list -> 'a1 -> 'a1) -> coq_Range -> nat list ->
  coq_R__range2list -> 'a1

val coq_R__range2list_rec :
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> nat list ->
  coq_R__range2list -> 'a1 -> 'a1) -> coq_Range -> nat list ->
  coq_R__range2list -> 'a1

val _range2list_rect :
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) ->
  coq_Range -> 'a1

val _range2list_rec :
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
  (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) ->
  coq_Range -> 'a1

val coq_R__range2list_correct : coq_Range -> nat list -> coq_R__range2list

val range2list_1 : nat -> nat -> nat list

val mifk :
  bool -> 'a1 option -> 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val mswitchk :
  (bool*'a1 option) list -> 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val mmap : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val mjoin : 'a1 option option -> 'a1 option

val mlift : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val mlift2 : ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option

val mlift3 :
  ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 option -> 'a2 option -> 'a3 option -> 'a4
  option

