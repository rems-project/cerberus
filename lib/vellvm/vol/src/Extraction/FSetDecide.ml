open Datatypes
open FSetFacts
open FSetInterface

module WDecide_fun = 
 functor (E:DecidableType.DecidableType) ->
 functor (M:sig 
  type elt = E.t
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val eq_dec : t -> t -> bool
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> t*t
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
 end) ->
 struct 
  module F = WFacts_fun(E)(M)
  
  module FSetLogicalFacts = 
   struct 
    
   end
  
  module FSetDecideAuxiliary = 
   struct 
    
   end
  
  module FSetDecideTestCases = 
   struct 
    
   end
 end

module WDecide = 
 functor (M:WS) ->
 WDecide_fun(M.E)(M)

module Decide = WDecide

