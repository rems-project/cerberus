open Bool
open Datatypes
open FSetInterface
open List0
open ListSet
open Maps
open MetatheoryAtom
open Wf_nat

type __ = Obj.t

module type SEMILATTICE = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

module type SEMILATTICE_WITH_TOP = 
 sig 
  type t 
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
  
  val top : t
 end

module LPMap : 
 functor (L:SEMILATTICE_WITH_TOP) ->
 sig 
  type t_ =
    | Bot_except of L.t ATree.t
    | Top_except of L.t ATree.t
  
  val t__rect : (L.t ATree.t -> 'a1) -> (L.t ATree.t -> 'a1) -> t_ -> 'a1
  
  val t__rec : (L.t ATree.t -> 'a1) -> (L.t ATree.t -> 'a1) -> t_ -> 'a1
  
  type t = t_
  
  val get : AtomImpl.atom -> t -> L.t
  
  val set : AtomImpl.atom -> L.t -> t -> t
  
  val beq : t -> t -> bool
  
  val bot : t_
  
  val top : t_
  
  val opt_lub : L.t -> L.t -> L.t option
  
  val lub : t -> t -> t
 end

module LFSet : 
 functor (S:S) ->
 sig 
  type t = S.t
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val lub : t -> t -> t
 end

module LFlat : 
 functor (X:EQUALITY_TYPE) ->
 sig 
  type t_ =
    | Bot
    | Inj of X.t
    | Top
  
  val t__rect : 'a1 -> (X.t -> 'a1) -> 'a1 -> t_ -> 'a1
  
  val t__rec : 'a1 -> (X.t -> 'a1) -> 'a1 -> t_ -> 'a1
  
  type t = t_
  
  val beq : t -> t -> bool
  
  val bot : t
  
  val top : t
  
  val lub : t -> t -> t
 end

module LBoolean : 
 sig 
  type t = bool
  
  val beq : t -> t -> bool
  
  val bot : bool
  
  val top : bool
  
  val lub : t -> t -> bool
 end

module AtomSet : 
 sig 
  type incl_dec_prop = AtomImpl.atom list -> AtomImpl.atom list -> __ -> bool
  
  val incl_dec_aux : nat -> AtomImpl.atom list -> AtomImpl.atom list -> bool
  
  val incl_dec : AtomImpl.atom list -> AtomImpl.atom list -> bool
  
  val set_eq_dec : AtomImpl.atom set -> AtomImpl.atom set -> bool
 end

module Dominators : 
 sig 
  type coq_BoundedSet =
    AtomImpl.atom set
    (* singleton inductive, whose constructor was mkBoundedSet *)
  
  val coq_BoundedSet_rect :
    AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
    -> 'a1
  
  val coq_BoundedSet_rec :
    AtomImpl.atom set -> (AtomImpl.atom set -> __ -> 'a1) -> coq_BoundedSet
    -> 'a1
  
  val bs_contents : AtomImpl.atom set -> coq_BoundedSet -> AtomImpl.atom set
  
  type t = coq_BoundedSet
  
  val eq_dec : AtomImpl.atom set -> t -> t -> bool
  
  val beq : AtomImpl.atom set -> t -> t -> bool
  
  val top : AtomImpl.atom set -> t
  
  val bot : AtomImpl.atom set -> t
  
  val lub : AtomImpl.atom set -> t -> t -> t
  
  val add : AtomImpl.atom set -> t -> AtomImpl.atom -> t
  
  val lubs : AtomImpl.atom set -> t list -> t
 end

