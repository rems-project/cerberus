open Datatypes
open FMapList
open Int0
open Peano

type __ = Obj.t

module Raw : 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 sig 
  type key = X.t
  
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.int
  
  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int -> 'a2)
    -> 'a1 tree -> 'a2
  
  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int -> 'a2)
    -> 'a1 tree -> 'a2
  
  val height : 'a1 tree -> I.int
  
  val cardinal : 'a1 tree -> nat
  
  val empty : 'a1 tree
  
  val is_empty : 'a1 tree -> bool
  
  val mem : X.t -> 'a1 tree -> bool
  
  val find : X.t -> 'a1 tree -> 'a1 option
  
  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
  
  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
  
  val remove : X.t -> 'a1 tree -> 'a1 tree
  
  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
  
  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }
  
  val triple_rect :
    ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
  
  val triple_rec :
    ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
  
  val t_left : 'a1 triple -> 'a1 tree
  
  val t_opt : 'a1 triple -> 'a1 option
  
  val t_right : 'a1 triple -> 'a1 tree
  
  val split : X.t -> 'a1 tree -> 'a1 triple
  
  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
  
  val elements_aux : (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
  
  val elements : 'a1 tree -> (key, 'a1) prod list
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
  
  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration
  
  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2
  
  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2
  
  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
  
  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool
  
  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool
  
  val equal_end : 'a1 enumeration -> bool
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
  
  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
  
  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree
  
  module Proofs : 
   sig 
    module MX : 
     sig 
      module OrderElts : 
       sig 
        type t = X.t
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
    
    module PX : 
     sig 
      module MO : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    module L : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      type key = X.t
      
      type 'elt t = (X.t, 'elt) prod list
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val mem : key -> 'a1 t -> bool
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
         * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
      
      val find : key -> 'a1 t -> 'a1 option
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
         * 'elt coq_R_find
      
      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      
      val remove : key -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      
      val elements : 'a1 t -> 'a1 t
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
      | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
         * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
      
      val coq_R_fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val coq_R_fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
      
      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
      
      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val option_cons :
        key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
      
      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
      
      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
      
      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
      
      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
        'a3) prod list
      
      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
      
      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * bool * 'elt coq_R_mem
    
    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
      -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
      __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
      -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
      __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt option * 'elt coq_R_find
    
    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
       I.int
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
       I.int
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
    
    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
      -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
      -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2) ->
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree
      -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key ->
      'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
    
    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
      -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
      -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
      -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2) ->
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree
      -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key ->
      'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * 'elt coq_R_add
    
    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
      'a2
    
    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
      'a2
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.int * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod
    
    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
      'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min ->
      'a2
    
    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
      'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min ->
      'a2
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt tree * key * 'elt * 'elt tree * I.int * 'elt tree
       * (key, 'elt) prod * key * 'elt
    
    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
      (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
    
    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
      (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
      tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.int * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.int * 'elt tree * 'elt coq_R_remove
    
    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
    
    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.int
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt tree * (key, 'elt) prod
    
    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
      (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_concat -> 'a2
    
    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
      (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
      'a1 coq_R_concat -> 'a2
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    
    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
      option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
      coq_R_split -> 'a2
    
    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
      option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
      coq_R_split -> 'a2
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
       * 'elt' tree * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.int * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    
    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'elt' tree
    | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int
    | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
       I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
       I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.int ->
      __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree
      -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __
      -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree
      -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
    
    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
      -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.int ->
      __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree
      -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __
      -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree
      -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
    
    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
   end
 end

module IntMake : 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
  
  module Raw : 
   sig 
    type key = X.t
    
    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.int
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> I.int
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree
         * I.int
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree
         * I.int
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.int
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.int * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
         * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val this : 'a1 bst -> 'a1 Raw.tree
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val find : key -> 'a1 t -> 'a1 option
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module IntMake_ord : 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 sig 
  module Data : 
   sig 
    type t = D.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
  
  module MapS : 
   sig 
    module E : 
     sig 
      type t = X.t
      
      val compare : t -> t -> t OrderedType.coq_Compare
      
      val eq_dec : t -> t -> bool
     end
    
    module Raw : 
     sig 
      type key = X.t
      
      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * I.int
      
      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
        'a2) -> 'a1 tree -> 'a2
      
      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
        'a2) -> 'a1 tree -> 'a2
      
      val height : 'a1 tree -> I.int
      
      val cardinal : 'a1 tree -> nat
      
      val empty : 'a1 tree
      
      val is_empty : 'a1 tree -> bool
      
      val mem : X.t -> 'a1 tree -> bool
      
      val find : X.t -> 'a1 tree -> 'a1 option
      
      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod
      
      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val remove : X.t -> 'a1 tree -> 'a1 tree
      
      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }
      
      val triple_rect :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val triple_rec :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val t_left : 'a1 triple -> 'a1 tree
      
      val t_opt : 'a1 triple -> 'a1 option
      
      val t_right : 'a1 triple -> 'a1 tree
      
      val split : X.t -> 'a1 tree -> 'a1 triple
      
      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val elements_aux :
        (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
      
      val elements : 'a1 tree -> (key, 'a1) prod list
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration
      
      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
      
      val equal_more :
        ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) ->
        'a1 enumeration -> bool
      
      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool
      
      val equal_end : 'a1 enumeration -> bool
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
      
      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
      
      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree
      
      module Proofs : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        module L : 
         sig 
          module MX : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
          
          module PX : 
           sig 
            module MO : 
             sig 
              module OrderElts : 
               sig 
                type t = X.t
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec : X.t -> X.t -> bool
              
              val lt_dec : X.t -> X.t -> bool
              
              val eqb : X.t -> X.t -> bool
             end
           end
          
          type key = X.t
          
          type 'elt t = (X.t, 'elt) prod list
          
          val empty : 'a1 t
          
          val is_empty : 'a1 t -> bool
          
          val mem : key -> 'a1 t -> bool
          
          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
             bool * 'elt coq_R_mem
          
          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
          
          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
          
          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
          
          val find : key -> 'a1 t -> 'a1 option
          
          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * 'elt option * 'elt coq_R_find
          
          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          
          val add : key -> 'a1 -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
             'elt t * 'elt coq_R_add
          
          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2
          
          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
          
          val remove : key -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * 'elt t * 'elt coq_R_remove
          
          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2
          
          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2
          
          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_remove_correct :
            key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          
          val elements : 'a1 t -> 'a1 t
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
          
          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
          | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
             'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
          
          val coq_R_fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2
            -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 ->
            ('a1, 'a3) coq_R_fold -> 'a2
          
          val coq_R_fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2
            -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 ->
            ('a1, 'a3) coq_R_fold -> 'a2
          
          val fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3
            -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3
            -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
          
          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * X.t * 'elt * (X.t, 'elt) prod list
             * X.t OrderedType.coq_Compare
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
          
          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1
            -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
            list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1
            -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
            list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
            __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
            OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
            'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
          
          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
            __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
            OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
            'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
          
          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
          
          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val option_cons :
            key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
          
          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
          
          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t
          
          val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
          
          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
          
          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key, 'a3) prod list
          
          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
          
          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * bool * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
          -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
          'a2
        
        val coq_R_mem_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
          -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem ->
          'a2
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option
          -> 'a1 coq_R_find -> 'a2
        
        val coq_R_find_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option
          -> 'a1 coq_R_find -> 'a2
        
        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt
           * 'elt tree * I.int
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt
           * 'elt tree * I.int
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
        
        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
          -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
          'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
          -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
          -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
        
        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree
          -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
          'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
          -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
          -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt tree * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_add -> 'a2
        
        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * I.int
           * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
           * 'elt tree * (key, 'elt) prod
        
        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * I.int
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt tree * (key, 'elt) prod * key * 'elt
        
        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree
          -> (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
        
        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree
          -> (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree ->
          'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * I.int * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * I.int
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * I.int * 'elt tree * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2
        
        val coq_R_remove_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2
        
        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * I.int
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt tree * (key, 'elt) prod
        
        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree
          -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_concat -> 'a2
        
        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree
          -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
          tree -> 'a1 coq_R_concat -> 'a2
        
        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
           * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
           I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
           * 'elt tree
        
        val coq_R_split_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
          coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
          coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
          'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
        
        val coq_R_split_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
          coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
          __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
          coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
          'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2
        
        type ('elt, 'elt') coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * I.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
           * 'elt' tree * ('elt, 'elt') coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * I.int * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
           * ('elt, 'elt') coq_R_map_option
        
        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __
          -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3
        
        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __
          -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
          coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3
        
        type ('elt, 'elt', 'elt'') coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'elt' tree
        | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * I.int
        | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree
           * I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
           * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree
           * I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt
        
        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 ->
          'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
          -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.int -> __ ->
          'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
          'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
          -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
        
        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 ->
          'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
          -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
          -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.int -> __ ->
          'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
          'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
          -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
        
        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
        
        val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
       end
     end
    
    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)
    
    val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val this : 'a1 bst -> 'a1 Raw.tree
    
    type 'elt t = 'elt bst
    
    type key = E.t
    
    val empty : 'a1 t
    
    val is_empty : 'a1 t -> bool
    
    val add : key -> 'a1 -> 'a1 t -> 'a1 t
    
    val remove : key -> 'a1 t -> 'a1 t
    
    val mem : key -> 'a1 t -> bool
    
    val find : key -> 'a1 t -> 'a1 option
    
    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
    
    val elements : 'a1 t -> (key, 'a1) prod list
    
    val cardinal : 'a1 t -> nat
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end
  
  module LO : 
   sig 
    module Data : 
     sig 
      type t = D.t
      
      val compare : t -> t -> t OrderedType.coq_Compare
      
      val eq_dec : t -> t -> bool
     end
    
    module MapS : 
     sig 
      module Raw : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      module E : 
       sig 
        type t = X.t
        
        val compare : t -> t -> t OrderedType.coq_Compare
        
        val eq_dec : t -> t -> bool
       end
      
      type key = E.t
      
      type 'elt slist =
        'elt Raw.t
        (* singleton inductive, whose constructor was Build_slist *)
      
      val slist_rect : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2
      
      val slist_rec : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2
      
      val this : 'a1 slist -> 'a1 Raw.t
      
      type 'elt t = 'elt slist
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      val find : key -> 'a1 t -> 'a1 option
      
      val remove : key -> 'a1 t -> 'a1 t
      
      val mem : key -> 'a1 t -> bool
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val elements : 'a1 t -> (key, 'a1) prod list
      
      val cardinal : 'a1 t -> nat
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end
    
    module MD : 
     sig 
      module OrderElts : 
       sig 
        type t = D.t
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : D.t -> D.t -> bool
      
      val lt_dec : D.t -> D.t -> bool
      
      val eqb : D.t -> D.t -> bool
     end
    
    type t = D.t MapS.t
    
    val cmp : D.t -> D.t -> bool
    
    val compare :
      D.t MapS.slist -> D.t MapS.slist -> D.t MapS.slist
      OrderedType.coq_Compare
   end
  
  module R : 
   sig 
    type key = X.t
    
    type 'elt tree = 'elt MapS.Raw.tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.int
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.int ->
      'a2) -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> I.int
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration = 'elt MapS.Raw.enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
        coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree
         * I.int
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree
         * I.int
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
        __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
        __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int
        -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add
        -> 'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.int
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
        -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt tree * key * 'elt * 'elt tree * I.int
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.int
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.int * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split ->
        'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree
        -> 'a1 triple -> 'a1 coq_R_split -> 'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.int * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
         * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * I.int * 'elt' tree * key * 'elt' * 'elt' tree * 
         I.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
        I.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __
        -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.int -> __ -> 'a2 tree
        -> key -> 'a2 -> 'a2 tree -> I.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
        'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt ->
        'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  module P : 
   sig 
    module MX : 
     sig 
      module OrderElts : 
       sig 
        type t = X.t
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
    
    module PX : 
     sig 
      module MO : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    module L : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      type key = X.t
      
      type 'elt t = (X.t, 'elt) prod list
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val mem : key -> 'a1 t -> bool
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
         * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
      
      val find : key -> 'a1 t -> 'a1 option
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
         * 'elt coq_R_find
      
      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      
      val remove : key -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      
      val elements : 'a1 t -> 'a1 t
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
      | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
         * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
      
      val coq_R_fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val coq_R_fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
      
      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
      
      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val option_cons :
        key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
      
      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
      
      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
      
      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
      
      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
        'a3) prod list
      
      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
      
      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt MapS.Raw.tree
    | R_mem_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * bool * 'elt coq_R_mem
    | R_mem_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_mem_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * bool * 'elt coq_R_mem
    
    val coq_R_mem_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      MapS.Raw.tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    val coq_R_mem_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      MapS.Raw.tree -> bool -> 'a1 coq_R_mem -> 'a2
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt MapS.Raw.tree
    | R_find_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_find_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt option * 'elt coq_R_find
    
    val coq_R_find_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
      -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    val coq_R_find_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
      -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_bal_1 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int
    | R_bal_2 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int
    | R_bal_3 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_bal_4 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_bal_5 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int
    | R_bal_6 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int
    | R_bal_7 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_bal_8 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    
    val coq_R_bal_rect :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 coq_R_bal -> 'a2
    
    val coq_R_bal_rec :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> __
      -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 coq_R_bal -> 'a2
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt MapS.Raw.tree
    | R_add_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * 'elt coq_R_add
    | R_add_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_add_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * 'elt coq_R_add
    
    val coq_R_add_rect :
      MapS.Raw.key -> 'a1 -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> 'a1 coq_R_add -> 'a2
    
    val coq_R_add_rec :
      MapS.Raw.key -> 'a1 -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> 'a1 coq_R_add -> 'a2
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_remove_min_1 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int
       * ('elt MapS.Raw.tree, (MapS.Raw.key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod
    
    val coq_R_remove_min_rect :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod) prod ->
      'a1 coq_R_remove_min -> 'a2 -> 'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1)
      prod -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod) prod ->
      'a1 coq_R_remove_min -> 'a2
    
    val coq_R_remove_min_rec :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod) prod ->
      'a1 coq_R_remove_min -> 'a2 -> 'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1)
      prod -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod) prod ->
      'a1 coq_R_remove_min -> 'a2
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
    | R_merge_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int
    | R_merge_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod * MapS.Raw.key * 'elt
    
    val coq_R_merge_rect :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1
      MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> MapS.Raw.key -> 'a1
      -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_merge -> 'a2
    
    val coq_R_merge_rec :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1
      MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> MapS.Raw.key -> 'a1
      -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_merge -> 'a2
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt MapS.Raw.tree
    | R_remove_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * 'elt coq_R_remove
    | R_remove_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_remove_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * 'elt coq_R_remove
    
    val coq_R_remove_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> 'a1 coq_R_remove -> 'a2
    
    val coq_R_remove_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_remove -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> 'a1 coq_R_remove -> 'a2
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
    | R_concat_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int
    | R_concat_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod
    
    val coq_R_concat_rect :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1
      MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_concat -> 'a2
    
    val coq_R_concat_rec :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a1
      MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_concat -> 'a2
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt MapS.Raw.tree
    | R_split_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.triple
       * 'elt coq_R_split * 'elt MapS.Raw.tree * 'elt option
       * 'elt MapS.Raw.tree
    | R_split_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int
    | R_split_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * I.int * 'elt MapS.Raw.triple
       * 'elt coq_R_split * 'elt MapS.Raw.tree * 'elt option
       * 'elt MapS.Raw.tree
    
    val coq_R_split_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2 -> 'a1
      MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split ->
      'a2 -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split ->
      'a2
    
    val coq_R_split_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2 -> 'a1
      MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> I.int -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      I.int -> __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split ->
      'a2 -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split ->
      'a2
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt MapS.Raw.tree
    | R_map_option_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * I.int * 'elt'
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * I.int
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
    
    val coq_R_map_option_rect :
      (MapS.Raw.key -> 'a1 -> 'a2 option) -> ('a1 MapS.Raw.tree -> __ -> 'a3)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 -> __ -> 'a2 MapS.Raw.tree ->
      ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 MapS.Raw.tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> 'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
      'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    val coq_R_map_option_rec :
      (MapS.Raw.key -> 'a1 -> 'a2 option) -> ('a1 MapS.Raw.tree -> __ -> 'a3)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 -> __ -> 'a2 MapS.Raw.tree ->
      ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 MapS.Raw.tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> I.int ->
      __ -> __ -> 'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
      'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option ->
      'a3
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
    | R_map2_opt_1 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int
    | R_map2_opt_2 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int * 'elt' MapS.Raw.tree * MapS.Raw.key * 'elt'
       * 'elt' MapS.Raw.tree * I.int * 'elt' MapS.Raw.tree * 'elt' option
       * 'elt' MapS.Raw.tree * 'elt'' * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * I.int * 'elt' MapS.Raw.tree * MapS.Raw.key * 'elt'
       * 'elt' MapS.Raw.tree * I.int * 'elt' MapS.Raw.tree * 'elt' option
       * 'elt' MapS.Raw.tree * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    val coq_R_map2_opt_rect :
      (MapS.Raw.key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 MapS.Raw.tree
      -> 'a3 MapS.Raw.tree) -> ('a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree) ->
      ('a1 MapS.Raw.tree -> 'a2 MapS.Raw.tree -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 MapS.Raw.tree ->
      MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> I.int -> __ -> 'a2
      MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> 'a3 -> __ ->
      'a3 MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 MapS.Raw.tree ->
      MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> I.int -> __ -> 'a2
      MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> __ -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree -> ('a1, 'a2,
      'a3) coq_R_map2_opt -> 'a4
    
    val coq_R_map2_opt_rec :
      (MapS.Raw.key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 MapS.Raw.tree
      -> 'a3 MapS.Raw.tree) -> ('a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree) ->
      ('a1 MapS.Raw.tree -> 'a2 MapS.Raw.tree -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 MapS.Raw.tree ->
      MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> I.int -> __ -> 'a2
      MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> 'a3 -> __ ->
      'a3 MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> I.int -> __ -> 'a2 MapS.Raw.tree ->
      MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> I.int -> __ -> 'a2
      MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> __ -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree -> ('a1, 'a2,
      'a3) coq_R_map2_opt -> 'a4
    
    val fold' :
      (MapS.Raw.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a2 -> 'a2
    
    val flatten_e : 'a1 MapS.Raw.enumeration -> (MapS.Raw.key, 'a1) prod list
   end
  
  type t = D.t MapS.t
  
  val cmp : D.t -> D.t -> bool
  
  val compare_more :
    X.t -> D.t -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
    comparison
  
  val compare_cont :
    D.t R.tree -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
    comparison
  
  val compare_end : D.t R.enumeration -> comparison
  
  val compare_pure : D.t R.tree -> D.t R.tree -> comparison
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val selements : t -> D.t LO.MapS.slist
 end

module Make : 
 functor (X:OrderedType.OrderedType) ->
 sig 
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
  
  module Raw : 
   sig 
    type key = X.t
    
    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> Z_as_Int.int
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        option -> 'a1 coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        option -> 'a1 coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal ->
        'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal ->
        'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 coq_R_add -> 'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.int
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
        -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
        -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
        -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
        -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
        'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
        'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.int * 'elt' tree * 'elt' option * 'elt' tree
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree
        -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ ->
        __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree
        -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ ->
        __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
  
  val this : 'a1 bst -> 'a1 Raw.tree
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val find : key -> 'a1 t -> 'a1 option
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make_ord : 
 functor (X:OrderedType.OrderedType) ->
 functor (D:OrderedType.OrderedType) ->
 sig 
  module Data : 
   sig 
    type t = D.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
  
  module MapS : 
   sig 
    module E : 
     sig 
      type t = X.t
      
      val compare : t -> t -> t OrderedType.coq_Compare
      
      val eq_dec : t -> t -> bool
     end
    
    module Raw : 
     sig 
      type key = X.t
      
      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
      
      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
      
      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
      
      val height : 'a1 tree -> Z_as_Int.int
      
      val cardinal : 'a1 tree -> nat
      
      val empty : 'a1 tree
      
      val is_empty : 'a1 tree -> bool
      
      val mem : X.t -> 'a1 tree -> bool
      
      val find : X.t -> 'a1 tree -> 'a1 option
      
      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod
      
      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val remove : X.t -> 'a1 tree -> 'a1 tree
      
      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
      
      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }
      
      val triple_rect :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val triple_rec :
        ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
      
      val t_left : 'a1 triple -> 'a1 tree
      
      val t_opt : 'a1 triple -> 'a1 option
      
      val t_right : 'a1 triple -> 'a1 tree
      
      val split : X.t -> 'a1 tree -> 'a1 triple
      
      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
      
      val elements_aux :
        (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
      
      val elements : 'a1 tree -> (key, 'a1) prod list
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration
      
      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2
      
      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
      
      val equal_more :
        ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) ->
        'a1 enumeration -> bool
      
      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool
      
      val equal_end : 'a1 enumeration -> bool
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
      
      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
      
      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
      
      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree
      
      module Proofs : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        module L : 
         sig 
          module MX : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
          
          module PX : 
           sig 
            module MO : 
             sig 
              module OrderElts : 
               sig 
                type t = X.t
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec : X.t -> X.t -> bool
              
              val lt_dec : X.t -> X.t -> bool
              
              val eqb : X.t -> X.t -> bool
             end
           end
          
          type key = X.t
          
          type 'elt t = (X.t, 'elt) prod list
          
          val empty : 'a1 t
          
          val is_empty : 'a1 t -> bool
          
          val mem : key -> 'a1 t -> bool
          
          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
             bool * 'elt coq_R_mem
          
          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
          
          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
          
          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
          
          val find : key -> 'a1 t -> 'a1 option
          
          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * 'elt option * 'elt coq_R_find
          
          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option ->
            'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2
          
          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          
          val add : key -> 'a1 -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
             'elt t * 'elt coq_R_add
          
          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1
            t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
            coq_R_add -> 'a2
          
          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2
          
          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2
            -> 'a2) -> 'a1 t -> 'a2
          
          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
          
          val remove : key -> 'a1 t -> 'a1 t
          
          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
          | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * 'elt t * 'elt coq_R_remove
          
          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2
          
          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2
          
          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
            prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
            -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2)
            -> 'a1 t -> 'a2
          
          val coq_R_remove_correct :
            key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          
          val elements : 'a1 t -> 'a1 t
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
          
          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
          | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
             'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
          
          val coq_R_fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2
            -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 ->
            ('a1, 'a3) coq_R_fold -> 'a2
          
          val coq_R_fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2
            -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 ->
            ('a1, 'a3) coq_R_fold -> 'a2
          
          val fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3
            -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 ->
            (X.t, 'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3
            -> 'a3) -> 'a1 t -> 'a3 -> 'a2
          
          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
          
          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
             * X.t * 'elt * (X.t, 'elt) prod list
             * X.t OrderedType.coq_Compare
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
          
          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1
            -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
            list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1
            -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
            list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
            'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
          
          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
            __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
            OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
            'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
          
          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
            X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
            __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
            OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
            'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
          
          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
          
          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
          
          val option_cons :
            key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
          
          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
          
          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t
          
          val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
          
          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
          
          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key, 'a3) prod list
          
          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
          
          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * bool * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
          __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
          'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
          __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
          'a1 coq_R_mem -> 'a2
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2
        
        val coq_R_find_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option ->
          'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 option -> 'a1 coq_R_find -> 'a2
        
        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.int
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.int
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
        
        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
          -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
          tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
          'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
        
        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ ->
          __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
          -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
          -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
          tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
          tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
          'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
          -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
          __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
          __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
          tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
        
        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Z_as_Int.int
           * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
           * 'elt tree * (key, 'elt) prod
        
        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ ->
          'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1)
          prod) prod -> 'a1 coq_R_remove_min -> 'a2
        
        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.int
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * (key, 'elt) prod * key * 'elt
        
        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
          'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2
        
        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
          'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
        
        val coq_R_remove_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
          'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
          tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ ->
          __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
          -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
        
        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.int
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt tree * (key, 'elt) prod
        
        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
        
        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
        
        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        
        val coq_R_split_rect :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2
        
        val coq_R_split_rec :
          X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple ->
          'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
          triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
          tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
          'a2
        
        type ('elt, 'elt') coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt' * 'elt' tree
           * ('elt, 'elt') coq_R_map_option * 'elt' tree
           * ('elt, 'elt') coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Z_as_Int.int * 'elt' tree * ('elt, 'elt') coq_R_map_option
           * 'elt' tree * ('elt, 'elt') coq_R_map_option
        
        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2
          -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
          -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3
        
        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2
          -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
          -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3
        
        type ('elt, 'elt', 'elt'') coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'elt' tree
        | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.int
        | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt'
           * 'elt' tree * Z_as_Int.int * 'elt' tree * 'elt' option
           * 'elt' tree * 'elt'' * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
           * ('elt, 'elt', 'elt'') coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
           'elt * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt'
           * 'elt' tree * Z_as_Int.int * 'elt' tree * 'elt' option
           * 'elt' tree * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt
           * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt
        
        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key
          -> 'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option
          -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4
        
        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key
          -> 'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option
          -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4
        
        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
        
        val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
       end
     end
    
    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)
    
    val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
    
    val this : 'a1 bst -> 'a1 Raw.tree
    
    type 'elt t = 'elt bst
    
    type key = E.t
    
    val empty : 'a1 t
    
    val is_empty : 'a1 t -> bool
    
    val add : key -> 'a1 -> 'a1 t -> 'a1 t
    
    val remove : key -> 'a1 t -> 'a1 t
    
    val mem : key -> 'a1 t -> bool
    
    val find : key -> 'a1 t -> 'a1 option
    
    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
    
    val elements : 'a1 t -> (key, 'a1) prod list
    
    val cardinal : 'a1 t -> nat
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end
  
  module LO : 
   sig 
    module Data : 
     sig 
      type t = D.t
      
      val compare : t -> t -> t OrderedType.coq_Compare
      
      val eq_dec : t -> t -> bool
     end
    
    module MapS : 
     sig 
      module Raw : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      module E : 
       sig 
        type t = X.t
        
        val compare : t -> t -> t OrderedType.coq_Compare
        
        val eq_dec : t -> t -> bool
       end
      
      type key = E.t
      
      type 'elt slist =
        'elt Raw.t
        (* singleton inductive, whose constructor was Build_slist *)
      
      val slist_rect : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2
      
      val slist_rec : ('a1 Raw.t -> __ -> 'a2) -> 'a1 slist -> 'a2
      
      val this : 'a1 slist -> 'a1 Raw.t
      
      type 'elt t = 'elt slist
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      val find : key -> 'a1 t -> 'a1 option
      
      val remove : key -> 'a1 t -> 'a1 t
      
      val mem : key -> 'a1 t -> bool
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val elements : 'a1 t -> (key, 'a1) prod list
      
      val cardinal : 'a1 t -> nat
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end
    
    module MD : 
     sig 
      module OrderElts : 
       sig 
        type t = D.t
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : D.t -> D.t -> bool
      
      val lt_dec : D.t -> D.t -> bool
      
      val eqb : D.t -> D.t -> bool
     end
    
    type t = D.t MapS.t
    
    val cmp : D.t -> D.t -> bool
    
    val compare :
      D.t MapS.slist -> D.t MapS.slist -> D.t MapS.slist
      OrderedType.coq_Compare
   end
  
  module R : 
   sig 
    type key = X.t
    
    type 'elt tree = 'elt MapS.Raw.tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
    
    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
    
    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
    
    val height : 'a1 tree -> Z_as_Int.int
    
    val cardinal : 'a1 tree -> nat
    
    val empty : 'a1 tree
    
    val is_empty : 'a1 tree -> bool
    
    val mem : X.t -> 'a1 tree -> bool
    
    val find : X.t -> 'a1 tree -> 'a1 option
    
    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod
    
    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val remove : X.t -> 'a1 tree -> 'a1 tree
    
    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
    
    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }
    
    val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
    
    val t_left : 'a1 triple -> 'a1 tree
    
    val t_opt : 'a1 triple -> 'a1 option
    
    val t_right : 'a1 triple -> 'a1 tree
    
    val split : X.t -> 'a1 tree -> 'a1 triple
    
    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
    
    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list
    
    val elements : 'a1 tree -> (key, 'a1) prod list
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
    
    type 'elt enumeration = 'elt MapS.Raw.enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration
    
    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2
    
    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
    
    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool
    
    val equal_end : 'a1 enumeration -> bool
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
    
    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
    
    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
    
    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree
    
    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree
    
    module Proofs : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      module L : 
       sig 
        module MX : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
        
        module PX : 
         sig 
          module MO : 
           sig 
            module OrderElts : 
             sig 
              type t = X.t
             end
            
            module OrderTac : 
             sig 
              
             end
            
            val eq_dec : X.t -> X.t -> bool
            
            val lt_dec : X.t -> X.t -> bool
            
            val eqb : X.t -> X.t -> bool
           end
         end
        
        type key = X.t
        
        type 'elt t = (X.t, 'elt) prod list
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val mem : key -> 'a1 t -> bool
        
        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
           * 'elt coq_R_mem
        
        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
        
        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
        
        val find : key -> 'a1 t -> 'a1 option
        
        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * 'elt option * 'elt coq_R_find
        
        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2
        
        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
           * 'elt coq_R_add
        
        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
        
        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
        
        val remove : key -> 'a1 t -> 'a1 t
        
        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
           'elt t * 'elt coq_R_remove
        
        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
          coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2
        
        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
          prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
          t -> 'a2
        
        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
        
        val elements : 'a1 t -> 'a1 t
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
        | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 
           'elt * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
        
        val coq_R_fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val coq_R_fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2)
          -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
          coq_R_fold -> 'a2
        
        val fold_rect :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val fold_rec :
          (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
          -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
          'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3)
          -> 'a1 t -> 'a3 -> 'a2
        
        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
        
        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
           * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
        
        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1
          coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 ->
          (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
          __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t ->
          'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
          -> bool -> 'a1 coq_R_equal -> 'a2
        
        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t ->
          'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
          -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
          -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t ->
          __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
        
        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
        
        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
        
        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
        
        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
        
        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list
        
        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
        
        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * bool * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt option * 'elt coq_R_find
      
      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        option -> 'a1 coq_R_find -> 'a2
      
      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        option -> 'a1 coq_R_find -> 'a2
      
      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
      
      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal ->
        'a2
      
      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
        'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal ->
        'a2
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 coq_R_add -> 'a2
      
      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.int
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod
      
      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2
      
      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * (key, 'elt) prod * key * 'elt
      
      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
        -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
        -> 'a2
      
      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key -> 'a1
        -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge
        -> 'a2
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2
      
      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt tree * (key, 'elt) prod
      
      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2
      
      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      
      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
        'a2
      
      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
        'a2
      
      type ('elt, 'elt') coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.int * 'elt' tree * ('elt, 'elt') coq_R_map_option
         * 'elt' tree * ('elt, 'elt') coq_R_map_option
      
      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3
      
      type ('elt, 'elt', 'elt'') coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'elt' tree
      | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int
      | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.int * 'elt' tree * 'elt' option * 'elt' tree * 'elt''
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt' * 'elt' tree
         * Z_as_Int.int * 'elt' tree * 'elt' option * 'elt' tree
         * 'elt'' tree * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
         * ('elt, 'elt', 'elt'') coq_R_map2_opt
      
      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree
        -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ ->
        __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option ->
        'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree
        -> Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ ->
        __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4
      
      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
      
      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end
  
  module P : 
   sig 
    module MX : 
     sig 
      module OrderElts : 
       sig 
        type t = X.t
       end
      
      module OrderTac : 
       sig 
        
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
    
    module PX : 
     sig 
      module MO : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    module L : 
     sig 
      module MX : 
       sig 
        module OrderElts : 
         sig 
          type t = X.t
         end
        
        module OrderTac : 
         sig 
          
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      module PX : 
       sig 
        module MO : 
         sig 
          module OrderElts : 
           sig 
            type t = X.t
           end
          
          module OrderTac : 
           sig 
            
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      type key = X.t
      
      type 'elt t = (X.t, 'elt) prod list
      
      val empty : 'a1 t
      
      val is_empty : 'a1 t -> bool
      
      val mem : key -> 'a1 t -> bool
      
      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
         * 'elt coq_R_mem
      
      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
        'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
      
      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
      
      val find : key -> 'a1 t -> 'a1 option
      
      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
         * 'elt coq_R_find
      
      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
        'a2
      
      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
      
      val add : key -> 'a1 -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_add
      
      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
      
      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
        'a1 -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
        -> 'a2
      
      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      
      val remove : key -> 'a1 t -> 'a1 t
      
      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
         * 'elt coq_R_remove
      
      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
      
      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
        prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
      
      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      
      val elements : 'a1 t -> 'a1 t
      
      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
      
      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
      | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
         * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
      
      val coq_R_fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val coq_R_fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) ->
        (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3)
        coq_R_fold -> 'a2
      
      val fold_rect :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val fold_rec :
        (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__
        -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t,
        'a1) prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) ->
        'a1 t -> 'a3 -> 'a2
      
      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold
      
      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
      
      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list
         * X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
      
      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
        'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list
        -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
        OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1
        t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
        coq_R_equal -> 'a2
      
      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t ->
        'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
        (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __
        -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
        'a2) -> 'a1 t -> 'a1 t -> 'a2
      
      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal
      
      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
      
      val option_cons :
        key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list
      
      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
      
      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
      
      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
      
      val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t
      
      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3
      
      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
        'a3) prod list
      
      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
      
      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt MapS.Raw.tree
    | R_mem_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * bool * 'elt coq_R_mem
    | R_mem_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_mem_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * bool * 'elt coq_R_mem
    
    val coq_R_mem_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
      coq_R_mem -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> bool -> 'a1 coq_R_mem
      -> 'a2
    
    val coq_R_mem_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1
      coq_R_mem -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> bool -> 'a1 coq_R_mem
      -> 'a2
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt MapS.Raw.tree
    | R_find_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt option
       * 'elt coq_R_find
    | R_find_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_find_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt option
       * 'elt coq_R_find
    
    val coq_R_find_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key ->
      'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
      coq_R_find -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1
      coq_R_find -> 'a2
    
    val coq_R_find_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key ->
      'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1
      coq_R_find -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1
      coq_R_find -> 'a2
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_bal_1 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_2 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_3 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_4 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_bal_5 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_6 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_7 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_bal_8 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    
    val coq_R_bal_rect :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key ->
      'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_bal -> 'a2
    
    val coq_R_bal_rec :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __ -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key ->
      'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1
      -> 'a1 MapS.Raw.tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_bal -> 'a2
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt MapS.Raw.tree
    | R_add_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * 'elt coq_R_add
    | R_add_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_add_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * 'elt coq_R_add
    
    val coq_R_add_rect :
      MapS.Raw.key -> 'a1 -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __
      -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 coq_R_add -> 'a2
    
    val coq_R_add_rec :
      MapS.Raw.key -> 'a1 -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree ->
      'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __
      -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 coq_R_add -> 'a2
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree
    | R_remove_min_1 of 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int
       * ('elt MapS.Raw.tree, (MapS.Raw.key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod
    
    val coq_R_remove_min_rect :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod)
      prod -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 MapS.Raw.tree ->
      (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> ('a1 MapS.Raw.tree,
      (MapS.Raw.key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
    
    val coq_R_remove_min_rec :
      ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> __ ->
      'a2) -> ('a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> ('a1 MapS.Raw.tree, (MapS.Raw.key, 'a1) prod)
      prod -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 MapS.Raw.tree ->
      (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> ('a1 MapS.Raw.tree,
      (MapS.Raw.key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
    | R_merge_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int
    | R_merge_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod * MapS.Raw.key * 'elt
    
    val coq_R_merge_rect :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> MapS.Raw.key ->
      'a1 -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_merge -> 'a2
    
    val coq_R_merge_rec :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> MapS.Raw.key ->
      'a1 -> __ -> 'a2) -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_merge -> 'a2
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt MapS.Raw.tree
    | R_remove_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * 'elt coq_R_remove
    | R_remove_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_remove_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * 'elt coq_R_remove
    
    val coq_R_remove_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2
    
    val coq_R_remove_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove
      -> 'a2 -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1
      MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree
      -> 'a1 MapS.Raw.tree -> 'a1 coq_R_remove -> 'a2
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
    | R_concat_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int
    | R_concat_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt
       * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.tree
       * (MapS.Raw.key, 'elt) prod
    
    val coq_R_concat_rect :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_concat -> 'a2
    
    val coq_R_concat_rec :
      ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a1 MapS.Raw.tree -> (MapS.Raw.key, 'a1) prod -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> 'a1
      coq_R_concat -> 'a2
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt MapS.Raw.tree
    | R_split_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.triple
       * 'elt coq_R_split * 'elt MapS.Raw.tree * 'elt option
       * 'elt MapS.Raw.tree
    | R_split_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
    | R_split_3 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree * MapS.Raw.key
       * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt MapS.Raw.triple
       * 'elt coq_R_split * 'elt MapS.Raw.tree * 'elt option
       * 'elt MapS.Raw.tree
    
    val coq_R_split_rect :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1
      MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __
      -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2 -> 'a1
      MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2
    
    val coq_R_split_rec :
      X.t -> ('a1 MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1
      MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree ->
      Z_as_Int.int -> __ -> __ -> __ -> 'a1 MapS.Raw.triple -> 'a1
      coq_R_split -> 'a2 -> 'a1 MapS.Raw.tree -> 'a1 option -> 'a1
      MapS.Raw.tree -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree
      -> MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __
      -> __ -> 'a2) -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree ->
      MapS.Raw.key -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ ->
      __ -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2 -> 'a1
      MapS.Raw.tree -> 'a1 option -> 'a1 MapS.Raw.tree -> __ -> 'a2) -> 'a1
      MapS.Raw.tree -> 'a1 MapS.Raw.triple -> 'a1 coq_R_split -> 'a2
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt MapS.Raw.tree
    | R_map_option_1 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int * 'elt'
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt MapS.Raw.tree * 'elt MapS.Raw.tree
       * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree * Z_as_Int.int
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
       * 'elt' MapS.Raw.tree * ('elt, 'elt') coq_R_map_option
    
    val coq_R_map_option_rect :
      (MapS.Raw.key -> 'a1 -> 'a2 option) -> ('a1 MapS.Raw.tree -> __ -> 'a3)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 -> __ -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2 MapS.Raw.tree -> ('a1,
      'a2) coq_R_map_option -> 'a3 -> 'a2 MapS.Raw.tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> 'a1 MapS.Raw.tree -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3
    
    val coq_R_map_option_rec :
      (MapS.Raw.key -> 'a1 -> 'a2 option) -> ('a1 MapS.Raw.tree -> __ -> 'a3)
      -> ('a1 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 ->
      'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 -> __ -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
      MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key -> 'a1 -> 'a1
      MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a2 MapS.Raw.tree -> ('a1,
      'a2) coq_R_map_option -> 'a3 -> 'a2 MapS.Raw.tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> 'a1 MapS.Raw.tree -> 'a2
      MapS.Raw.tree -> ('a1, 'a2) coq_R_map_option -> 'a3
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
    | R_map2_opt_1 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int
    | R_map2_opt_2 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int * 'elt' MapS.Raw.tree * MapS.Raw.key * 'elt'
       * 'elt' MapS.Raw.tree * Z_as_Int.int * 'elt' MapS.Raw.tree
       * 'elt' option * 'elt' MapS.Raw.tree * 'elt'' * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt MapS.Raw.tree * 'elt' MapS.Raw.tree
       * 'elt MapS.Raw.tree * MapS.Raw.key * 'elt * 'elt MapS.Raw.tree
       * Z_as_Int.int * 'elt' MapS.Raw.tree * MapS.Raw.key * 'elt'
       * 'elt' MapS.Raw.tree * Z_as_Int.int * 'elt' MapS.Raw.tree
       * 'elt' option * 'elt' MapS.Raw.tree * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' MapS.Raw.tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    val coq_R_map2_opt_rect :
      (MapS.Raw.key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 MapS.Raw.tree
      -> 'a3 MapS.Raw.tree) -> ('a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree) ->
      ('a1 MapS.Raw.tree -> 'a2 MapS.Raw.tree -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 MapS.Raw.tree
      -> MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a2 MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> 'a3 -> __
      -> 'a3 MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 MapS.Raw.tree
      -> MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a2 MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> __ -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree -> ('a1, 'a2,
      'a3) coq_R_map2_opt -> 'a4
    
    val coq_R_map2_opt_rec :
      (MapS.Raw.key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 MapS.Raw.tree
      -> 'a3 MapS.Raw.tree) -> ('a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree) ->
      ('a1 MapS.Raw.tree -> 'a2 MapS.Raw.tree -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 MapS.Raw.tree
      -> MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a2 MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> 'a3 -> __
      -> 'a3 MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a1 MapS.Raw.tree -> MapS.Raw.key
      -> 'a1 -> 'a1 MapS.Raw.tree -> Z_as_Int.int -> __ -> 'a2 MapS.Raw.tree
      -> MapS.Raw.key -> 'a2 -> 'a2 MapS.Raw.tree -> Z_as_Int.int -> __ ->
      'a2 MapS.Raw.tree -> 'a2 option -> 'a2 MapS.Raw.tree -> __ -> __ -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
      MapS.Raw.tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1
      MapS.Raw.tree -> 'a2 MapS.Raw.tree -> 'a3 MapS.Raw.tree -> ('a1, 'a2,
      'a3) coq_R_map2_opt -> 'a4
    
    val fold' :
      (MapS.Raw.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 MapS.Raw.tree -> 'a2 -> 'a2
    
    val flatten_e : 'a1 MapS.Raw.enumeration -> (MapS.Raw.key, 'a1) prod list
   end
  
  type t = D.t MapS.t
  
  val cmp : D.t -> D.t -> bool
  
  val compare_more :
    X.t -> D.t -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
    comparison
  
  val compare_cont :
    D.t R.tree -> (D.t R.enumeration -> comparison) -> D.t R.enumeration ->
    comparison
  
  val compare_end : D.t R.enumeration -> comparison
  
  val compare_pure : D.t R.tree -> D.t R.tree -> comparison
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  val selements : t -> D.t LO.MapS.slist
 end

