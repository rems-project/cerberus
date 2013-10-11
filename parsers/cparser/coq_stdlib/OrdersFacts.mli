open Basics
open Datatypes
open Orders
open OrdersTac

module OrderedTypeFullFacts : 
 functor (O:OrderedTypeFull') ->
 sig 
  module OrderTac : 
   sig 
    module TO : 
     sig 
      type t = O.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> bool
     end
   end
 end

module OrderedTypeFacts : 
 functor (O:OrderedType') ->
 sig 
  module OrderTac : 
   sig 
    module OTF : 
     sig 
      type t = O.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> bool
     end
    
    module TO : 
     sig 
      type t = OTF.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> bool
     end
   end
  
  val eq_dec : O.t -> O.t -> bool
  
  val lt_dec : O.t -> O.t -> bool
  
  val eqb : O.t -> O.t -> bool
 end

module OrderedTypeTest : 
 functor (O:OrderedType') ->
 sig 
  module MO : 
   sig 
    module OrderTac : 
     sig 
      module OTF : 
       sig 
        type t = O.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> bool
       end
      
      module TO : 
       sig 
        type t = OTF.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> bool
       end
     end
    
    val eq_dec : O.t -> O.t -> bool
    
    val lt_dec : O.t -> O.t -> bool
    
    val eqb : O.t -> O.t -> bool
   end
 end

module OrderedTypeRev : 
 functor (O:OrderedTypeFull) ->
 sig 
  type t = O.t
  
  val eq_dec : O.t -> O.t -> bool
  
  val compare : O.t -> O.t -> comparison
 end

