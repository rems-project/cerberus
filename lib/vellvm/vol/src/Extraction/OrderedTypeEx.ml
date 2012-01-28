open BinInt
open BinNat
open BinPos
open Compare_dec
open Datatypes
open Peano_dec
open ZArith_dec

module type UsualOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val eq_dec : t -> t -> bool
 end

module UOT_to_OT = 
 functor (U:UsualOrderedType) ->
 U

module Nat_as_OT = 
 struct 
  type t = nat
  
  (** val compare : t -> t -> nat OrderedType.coq_Compare **)
  
  let compare x y =
    let c = nat_compare x y in
    (match c with
       | Eq -> OrderedType.EQ
       | Lt -> OrderedType.LT
       | Gt -> OrderedType.GT)
  
  (** val eq_dec : nat -> nat -> bool **)
  
  let eq_dec =
    eq_nat_dec
 end

module Z_as_OT = 
 struct 
  type t = coq_Z
  
  (** val compare : coq_Z -> coq_Z -> coq_Z OrderedType.coq_Compare **)
  
  let compare x y =
    let c = coq_Zcompare x y in
    (match c with
       | Eq -> OrderedType.EQ
       | Lt -> OrderedType.LT
       | Gt -> OrderedType.GT)
  
  (** val eq_dec : coq_Z -> coq_Z -> bool **)
  
  let eq_dec =
    coq_Z_eq_dec
 end

module Positive_as_OT = 
 struct 
  type t = positive
  
  (** val compare : t -> t -> positive OrderedType.coq_Compare **)
  
  let compare x y =
    let c = coq_Pcompare x y Eq in
    (match c with
       | Eq -> OrderedType.EQ
       | Lt -> OrderedType.LT
       | Gt -> OrderedType.GT)
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
      | Coq_xI p0 ->
          (match y0 with
             | Coq_xI p1 -> eq_dec p0 p1
             | _ -> false)
      | Coq_xO p0 ->
          (match y0 with
             | Coq_xO p1 -> eq_dec p0 p1
             | _ -> false)
      | Coq_xH -> (match y0 with
                     | Coq_xH -> true
                     | _ -> false)
 end

module N_as_OT = 
 struct 
  type t = coq_N
  
  (** val compare : t -> t -> coq_N OrderedType.coq_Compare **)
  
  let compare x y =
    let c = coq_Ncompare x y in
    (match c with
       | Eq -> OrderedType.EQ
       | Lt -> OrderedType.LT
       | Gt -> OrderedType.GT)
  
  (** val eq_dec : coq_N -> coq_N -> bool **)
  
  let eq_dec x y =
    match x with
      | N0 -> (match y with
                 | N0 -> true
                 | Npos p -> false)
      | Npos x0 ->
          (match y with
             | N0 -> false
             | Npos p0 -> Positive_as_OT.eq_dec x0 p0)
 end

module PairOrderedType = 
 functor (O1:OrderedType.OrderedType) ->
 functor (O2:OrderedType.OrderedType) ->
 struct 
  module MO1 = OrderedType.OrderedTypeFacts(O1)
  
  module MO2 = OrderedType.OrderedTypeFacts(O2)
  
  type t = O1.t*O2.t
  
  (** val compare : t -> t -> (O1.t*O2.t) OrderedType.coq_Compare **)
  
  let compare x y =
    let x1,x2 = x in
    let y1,y2 = y in
    let c = O1.compare x1 y1 in
    (match c with
       | OrderedType.LT -> OrderedType.LT
       | OrderedType.EQ ->
           let c0 = O2.compare x2 y2 in
           (match c0 with
              | OrderedType.LT -> OrderedType.LT
              | OrderedType.EQ -> OrderedType.EQ
              | OrderedType.GT -> OrderedType.GT)
       | OrderedType.GT -> OrderedType.GT)
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    match compare x y with
      | OrderedType.EQ -> true
      | _ -> false
 end

module PositiveOrderedTypeBits = 
 struct 
  type t = positive
  
  (** val compare : t -> t -> positive OrderedType.coq_Compare **)
  
  let rec compare p y =
    match p with
      | Coq_xI p0 ->
          (match y with
             | Coq_xI y0 -> compare p0 y0
             | _ -> OrderedType.GT)
      | Coq_xO p0 ->
          (match y with
             | Coq_xO y0 -> compare p0 y0
             | _ -> OrderedType.LT)
      | Coq_xH ->
          (match y with
             | Coq_xI y0 -> OrderedType.LT
             | Coq_xO y0 -> OrderedType.GT
             | Coq_xH -> OrderedType.EQ)
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let eq_dec x y =
    match coq_Pcompare x y Eq with
      | Eq -> true
      | _ -> false
 end

