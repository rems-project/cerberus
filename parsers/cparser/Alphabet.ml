open BinNat
open Compare_dec
open Datatypes
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_Comparable =
  'a -> 'a -> comparison
  (* singleton inductive, whose constructor was Build_Comparable *)

(** val coq_Comparable_rect :
    (('a1 -> 'a1 -> comparison) -> __ -> __ -> 'a2) -> 'a1 coq_Comparable ->
    'a2 **)

let coq_Comparable_rect f c =
  f c __ __

(** val coq_Comparable_rec :
    (('a1 -> 'a1 -> comparison) -> __ -> __ -> 'a2) -> 'a1 coq_Comparable ->
    'a2 **)

let coq_Comparable_rec f c =
  f c __ __

(** val compare : 'a1 coq_Comparable -> 'a1 -> 'a1 -> comparison **)

let compare comparable =
  comparable

(** val natComparable : nat coq_Comparable **)

let natComparable =
  nat_compare

(** val coq_PairComparable :
    'a1 coq_Comparable -> 'a2 coq_Comparable -> ('a1*'a2) coq_Comparable **)

let coq_PairComparable cA cB x y =
  let xa,xb = x in
  let ya,yb = y in
  (match compare cA xa ya with
     | Eq -> compare cB xb yb
     | _ -> compare cA xa ya)

(** val compare_eqb : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool **)

let compare_eqb c x y =
  match compare c x y with
    | Eq -> true
    | _ -> false

(** val compare_eqdec : 'a1 coq_Comparable -> 'a1 -> 'a1 -> bool **)

let compare_eqdec c x y =
  let c0 = compare c x y in (match c0 with
                               | Eq -> true
                               | _ -> false)

type 'a coq_Finite =
  'a list
  (* singleton inductive, whose constructor was Build_Finite *)

(** val coq_Finite_rect :
    ('a1 list -> __ -> 'a2) -> 'a1 coq_Finite -> 'a2 **)

let coq_Finite_rect f f0 =
  f f0 __

(** val coq_Finite_rec : ('a1 list -> __ -> 'a2) -> 'a1 coq_Finite -> 'a2 **)

let coq_Finite_rec f f0 =
  f f0 __

(** val all_list : 'a1 coq_Finite -> 'a1 list **)

let all_list finite =
  finite

type 'a coq_Alphabet = { coq_AlphabetComparable : 'a coq_Comparable;
                         coq_AlphabetFinite : 'a coq_Finite }

(** val coq_Alphabet_rect :
    ('a1 coq_Comparable -> __ -> 'a1 coq_Finite -> 'a2) -> 'a1 coq_Alphabet
    -> 'a2 **)

let coq_Alphabet_rect f a =
  let { coq_AlphabetComparable = x; coq_AlphabetFinite = x0 } = a in
  f x __ x0

(** val coq_Alphabet_rec :
    ('a1 coq_Comparable -> __ -> 'a1 coq_Finite -> 'a2) -> 'a1 coq_Alphabet
    -> 'a2 **)

let coq_Alphabet_rec f a =
  let { coq_AlphabetComparable = x; coq_AlphabetFinite = x0 } = a in
  f x __ x0

(** val coq_AlphabetComparable : 'a1 coq_Alphabet -> 'a1 coq_Comparable **)

let coq_AlphabetComparable x = x.coq_AlphabetComparable

(** val coq_AlphabetFinite : 'a1 coq_Alphabet -> 'a1 coq_Finite **)

let coq_AlphabetFinite x = x.coq_AlphabetFinite

type 'a coq_Numbered = { injN : ('a -> coq_N); surjN : 
                         (coq_N -> 'a); injN_bound : 
                         coq_N }

(** val coq_Numbered_rect :
    (('a1 -> coq_N) -> (coq_N -> 'a1) -> __ -> coq_N -> __ -> 'a2) -> 'a1
    coq_Numbered -> 'a2 **)

let coq_Numbered_rect f n =
  let { injN = x; surjN = x0; injN_bound = x1 } = n in f x x0 __ x1 __

(** val coq_Numbered_rec :
    (('a1 -> coq_N) -> (coq_N -> 'a1) -> __ -> coq_N -> __ -> 'a2) -> 'a1
    coq_Numbered -> 'a2 **)

let coq_Numbered_rec f n =
  let { injN = x; surjN = x0; injN_bound = x1 } = n in f x x0 __ x1 __

(** val injN : 'a1 coq_Numbered -> 'a1 -> coq_N **)

let injN x = x.injN

(** val surjN : 'a1 coq_Numbered -> coq_N -> 'a1 **)

let surjN x = x.surjN

(** val injN_bound : 'a1 coq_Numbered -> coq_N **)

let injN_bound x = x.injN_bound

(** val coq_NumberedAlphabet : 'a1 coq_Numbered -> 'a1 coq_Alphabet **)

let coq_NumberedAlphabet n =
  { coq_AlphabetComparable = (fun x y -> coq_Ncompare (n.injN x) (n.injN y));
    coq_AlphabetFinite =
    (coq_Nrect [] (fun n0 x -> (n.surjN n0)::x) n.injN_bound) }

(** val coq_OptionComparable :
    'a1 coq_Comparable -> 'a1 option coq_Comparable **)

let coq_OptionComparable c x y =
  match x with
    | Some x0 -> (match y with
                    | Some y0 -> compare c x0 y0
                    | None -> Gt)
    | None -> (match y with
                 | Some a -> Lt
                 | None -> Eq)

(** val coq_OptionFinite : 'a1 coq_Finite -> 'a1 option coq_Finite **)

let coq_OptionFinite e =
  None::(map (fun x -> Some x) (all_list e))

module type ComparableM = 
 sig 
  type t 
  
  val tComparable : t coq_Comparable
 end

module OrderedTypeAlt_from_ComparableM = 
 functor (C:ComparableM) ->
 struct 
  type t = C.t
  
  (** val compare : t -> t -> comparison **)
  
  let compare =
    compare C.tComparable
 end

module OrderedType_from_ComparableM = 
 functor (C:ComparableM) ->
 struct 
  module Alt = OrderedTypeAlt_from_ComparableM(C)
  
  type t = Alt.t
  
  (** val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare **)
  
  let compare x y =
    match Alt.compare x y with
      | Eq -> OrderedType.EQ
      | Lt -> OrderedType.LT
      | Gt -> OrderedType.GT
  
  (** val eq_dec : Alt.t -> Alt.t -> bool **)
  
  let eq_dec x y =
    match Alt.compare x y with
      | Eq -> true
      | _ -> false
 end

