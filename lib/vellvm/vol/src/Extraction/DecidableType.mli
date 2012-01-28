open Equalities

module type EqualityType = 
 EqualityTypeOrig

module type DecidableType = 
 DecidableTypeOrig

module KeyDecidableType : 
 functor (D:DecidableType) ->
 sig 
  
 end

