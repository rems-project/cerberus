open BinNat
open Compare_dec
open Datatypes
open List0

type __ = Obj.t

type 'a coq_Comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

val coq_Comparable_rect :
  (('a1 -> 'a1 -> comparison) -> __ -> __ -> 'a2) -> 'a1 coq_Comparable ->
  'a2

val coq_Comparable_rec :
  (('a1 -> 'a1 -> comparison) -> __ -> __ -> 'a2) -> 'a1 coq_Comparable ->
  'a2

val compare : 'a1 coq_Comparable -> 'a1 -> 'a1 -> comparison

val natComparable : nat coq_Comparable

val coq_PairComparable :
  'a1 coq_Comparable -> 'a2 coq_Comparable -> ('a1*'a2) coq_Comparable

val compare_eqb : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool

val compare_eqdec : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool

type 'a coq_Finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

val coq_Finite_rect : ('a1 list -> __ -> 'a2) -> 'a1 coq_Finite -> 'a2

val coq_Finite_rec : ('a1 list -> __ -> 'a2) -> 'a1 coq_Finite -> 'a2

val all_list : 'a1 coq_Finite -> 'a1 list

type 'a coq_Alphabet = { coq_AlphabetComparable : 'a coq_Comparable;
                         coq_AlphabetFinite : 'a coq_Finite }

val coq_Alphabet_rect :
  ('a1 coq_Comparable -> __ -> 'a1 coq_Finite -> 'a2) -> 'a1 coq_Alphabet ->
  'a2

val coq_Alphabet_rec :
  ('a1 coq_Comparable -> __ -> 'a1 coq_Finite -> 'a2) -> 'a1 coq_Alphabet ->
  'a2

val coq_AlphabetComparable : 'a1 coq_Alphabet -> 'a1 coq_Comparable

val coq_AlphabetFinite : 'a1 coq_Alphabet -> 'a1 coq_Finite

type 'a coq_Numbered = { injN : ('a -> coq_N); surjN : (coq_N -> 'a);
                         injN_bound : coq_N }

val coq_Numbered_rect :
  (('a1 -> coq_N) -> (coq_N -> 'a1) -> __ -> coq_N -> __ -> 'a2) -> 'a1
  coq_Numbered -> 'a2

val coq_Numbered_rec :
  (('a1 -> coq_N) -> (coq_N -> 'a1) -> __ -> coq_N -> __ -> 'a2) -> 'a1
  coq_Numbered -> 'a2

val injN : 'a1 coq_Numbered -> 'a1 -> coq_N

val surjN : 'a1 coq_Numbered -> coq_N -> 'a1

val injN_bound : 'a1 coq_Numbered -> coq_N

val coq_NumberedAlphabet : 'a1 coq_Numbered -> 'a1 coq_Alphabet

val coq_OptionComparable : 'a1 coq_Comparable -> 'a1 option coq_Comparable

val coq_OptionFinite : 'a1 coq_Finite -> 'a1 option coq_Finite

module type ComparableM = 
 sig 
  type t 
  
  val tComparable : t coq_Comparable
 end

module OrderedTypeAlt_from_ComparableM : 
 functor (C:ComparableM) ->
 sig 
  type t = C.t
  
  val compare : t -> t -> comparison
 end

module OrderedType_from_ComparableM : 
 functor (C:ComparableM) ->
 sig 
  module Alt : 
   sig 
    type t = C.t
    
    val compare : t -> t -> comparison
   end
  
  type t = Alt.t
  
  val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
  
  val eq_dec : Alt.t -> Alt.t -> bool
 end

