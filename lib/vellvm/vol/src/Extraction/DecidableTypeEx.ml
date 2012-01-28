open BinInt
open BinNat
open BinPos
open Datatypes
open OrderedTypeEx

module type UsualDecidableType = 
 Equalities.UsualDecidableTypeOrig

module UDT_to_DT = 
 functor (U:UsualDecidableType) ->
 U

module type MiniDecidableType = 
 Equalities.MiniDecidableType

module Make_UDT = 
 functor (M:MiniDecidableType) ->
 Equalities.Make_UDT(M)

module OT_as_DT = 
 functor (O:OrderedType.OrderedType) ->
 O

module Nat_as_DT = Nat_as_OT

module Positive_as_DT = Positive_as_OT

module N_as_DT = N_as_OT

module Z_as_DT = Z_as_OT

module PairDecidableType = 
 functor (D1:DecidableType.DecidableType) ->
 functor (D2:DecidableType.DecidableType) ->
 struct 
  type t = D1.t*D2.t
  
  (** val eq_dec : (D1.t*D2.t) -> (D1.t*D2.t) -> bool **)
  
  let eq_dec x y =
    let x1,x2 = x in
    let y1,y2 = y in
    let s = D1.eq_dec x1 y1 in if s then D2.eq_dec x2 y2 else false
 end

module PairUsualDecidableType = 
 functor (D1:UsualDecidableType) ->
 functor (D2:UsualDecidableType) ->
 struct 
  type t = D1.t*D2.t
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    let x1,x2 = x in
    let y1,y2 = y in
    let s = D1.eq_dec x1 y1 in if s then D2.eq_dec x2 y2 else false
 end

