open BinPos
open Coqlib
open Datatypes
open Specif

type __ = Obj.t

module type ITER = 
 sig 
  val iterate : ('a1 -> ('a2, 'a1) sum) -> 'a1 -> 'a2 option
 end

val dependent_description' : __ -> ('a1 -> 'a2, __) sigT

module PrimIter : 
 sig 
  val num_iterations : positive
  
  val iter_step :
    ('a1 -> ('a2, 'a1) sum) -> positive -> (positive -> __ -> 'a1 -> 'a2
    option) -> 'a1 -> 'a2 option
  
  val iter : ('a1 -> ('a2, 'a1) sum) -> positive -> 'a1 -> 'a2 option
  
  val iterate : ('a1 -> ('a2, 'a1) sum) -> 'a1 -> 'a2 option
 end

module SafePrimIter : 
 sig 
  val iter_step :
    ('a1 -> ('a1, 'a1) sum) -> positive -> (positive -> __ -> 'a1 -> 'a1) ->
    'a1 -> 'a1
  
  val iter : ('a1 -> ('a1, 'a1) sum) -> positive -> 'a1 -> 'a1
  
  val num_iterations : positive
  
  val iterate : ('a1 -> ('a1, 'a1) sum) -> 'a1 -> 'a1
 end

module GenIter : 
 ITER

