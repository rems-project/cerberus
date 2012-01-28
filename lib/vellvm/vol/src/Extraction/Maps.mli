open BinInt
open BinNat
open BinPos
open Coqlib
open Datatypes
open List0
open MetatheoryAtom
open Alist

module type TREE = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val empty : 'a1 t
  
  val get : elt -> 'a1 t -> 'a1 option
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : elt -> 'a1 t -> 'a1 t
  
  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val combine :
    ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t
  
  val elements : 'a1 t -> (elt*'a1) list
  
  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module type MAP = 
 sig 
  type elt 
  
  val elt_eq : elt -> elt -> bool
  
  type 'x t 
  
  val init : 'a1 -> 'a1 t
  
  val get : elt -> 'a1 t -> 'a1
  
  val set : elt -> 'a1 -> 'a1 t -> 'a1 t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PTree : 
 sig 
  type elt = positive
  
  val elt_eq : positive -> positive -> bool
  
  type 'a tree =
    | Leaf
    | Node of 'a tree * 'a option * 'a tree
  
  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
    tree -> 'a2
  
  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
    tree -> 'a2
  
  type 'a t = 'a tree
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val empty : 'a1 t
  
  val get : positive -> 'a1 t -> 'a1 option
  
  val set : positive -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : positive -> 'a1 t -> 'a1 t
  
  val bempty : 'a1 t -> bool
  
  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val append : positive -> positive -> positive
  
  val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t
  
  val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t
  
  val xcombine_l : ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t
  
  val xcombine_r : ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t
  
  val combine :
    ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t
  
  val xelements : 'a1 t -> positive -> (positive*'a1) list
  
  val elements : 'a1 t -> (positive*'a1) list
  
  val xget : positive -> positive -> 'a1 t -> 'a1 option
  
  val xkeys : 'a1 t -> positive -> positive list
  
  val xfold :
    ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2
  
  val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module ATree : 
 sig 
  type elt = AtomImpl.atom
  
  val elt_eq : AtomImpl.atom -> AtomImpl.atom -> bool
  
  type 'a tree = (AtomImpl.atom*'a) list
  
  type 'a t = 'a tree
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val empty : 'a1 t
  
  val get : AtomImpl.atom -> 'a1 t -> 'a1 option
  
  val set : AtomImpl.atom -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : AtomImpl.atom -> 'a1 t -> 'a1 t
  
  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val map : (elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val combine :
    ('a1 option -> 'a1 option -> 'a1 option) -> 'a1 t -> 'a1 t -> 'a1 t
  
  val elements : 'a1 t -> 'a1 t
  
  val fold : ('a2 -> elt -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module PMap : 
 sig 
  type elt = positive
  
  val elt_eq : positive -> positive -> bool
  
  type 'a t = 'a*'a PTree.t
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val init : 'a1 -> 'a1*'a1 PTree.t
  
  val get : positive -> 'a1 t -> 'a1
  
  val set : positive -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module AMap : 
 sig 
  type elt = AtomImpl.atom
  
  val elt_eq : AtomImpl.atom -> AtomImpl.atom -> bool
  
  type 'a t = 'a*'a ATree.t
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val init : 'a1 -> 'a1*'a1 ATree.t
  
  val get : AtomImpl.atom -> 'a1 t -> 'a1
  
  val set : AtomImpl.atom -> 'a1 -> 'a1 t -> 'a1*'a1 ATree.t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE = 
 sig 
  type t 
  
  val index : t -> positive
  
  val eq : t -> t -> bool
 end

module IMap : 
 functor (X:INDEXED_TYPE) ->
 sig 
  type elt = X.t
  
  val elt_eq : X.t -> X.t -> bool
  
  type 'x t = 'x PMap.t
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val init : 'a1 -> 'a1*'a1 PTree.t
  
  val get : X.t -> 'a1 t -> 'a1
  
  val set : X.t -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed : 
 sig 
  type t = coq_Z
  
  val index : coq_Z -> positive
  
  val eq : coq_Z -> coq_Z -> bool
 end

module ZMap : 
 sig 
  type elt = ZIndexed.t
  
  val elt_eq : ZIndexed.t -> ZIndexed.t -> bool
  
  type 'x t = 'x PMap.t
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val init : 'a1 -> 'a1*'a1 PTree.t
  
  val get : ZIndexed.t -> 'a1 t -> 'a1
  
  val set : ZIndexed.t -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module NIndexed : 
 sig 
  type t = coq_N
  
  val index : coq_N -> positive
  
  val eq : coq_N -> coq_N -> bool
 end

module NMap : 
 sig 
  type elt = NIndexed.t
  
  val elt_eq : NIndexed.t -> NIndexed.t -> bool
  
  type 'x t = 'x PMap.t
  
  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  val init : 'a1 -> 'a1*'a1 PTree.t
  
  val get : NIndexed.t -> 'a1 t -> 'a1
  
  val set : NIndexed.t -> 'a1 -> 'a1 t -> 'a1*'a1 PTree.t
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type EQUALITY_TYPE = 
 sig 
  type t 
  
  val eq : t -> t -> bool
 end

module EMap : 
 functor (X:EQUALITY_TYPE) ->
 sig 
  type elt = X.t
  
  val elt_eq : X.t -> X.t -> bool
  
  type 'a t = X.t -> 'a
  
  val init : 'a1 -> X.t -> 'a1
  
  val get : X.t -> 'a1 t -> 'a1
  
  val set : X.t -> 'a1 -> 'a1 t -> X.t -> 'a1
  
  val map : ('a1 -> 'a2) -> 'a1 t -> X.t -> 'a2
 end

module Tree_Properties : 
 functor (T:TREE) ->
 sig 
  val f' : ('a2 -> T.elt -> 'a1 -> 'a2) -> 'a2 -> (T.elt*'a1) -> 'a2
 end

module ATree_Properties : 
 sig 
  val f' : ('a2 -> ATree.elt -> 'a1 -> 'a2) -> 'a2 -> (ATree.elt*'a1) -> 'a2
 end

