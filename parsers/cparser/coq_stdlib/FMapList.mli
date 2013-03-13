open Datatypes
open List0

type __ = Obj.t

module Raw : 
 functor (X:OrderedType.OrderedType) ->
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
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
    -> bool -> 'a1 coq_R_mem -> 'a2
  
  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
    -> bool -> 'a1 coq_R_mem -> 'a2
  
  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
  
  val find : key -> 'a1 t -> 'a1 option
  
  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
     * 'elt coq_R_find
  
  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
  
  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
  
  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_add
  
  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
  
  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) ->
    'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
  
  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
    prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
  
  val remove : key -> 'a1 t -> 'a1 t
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_remove
  
  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
    t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
  
  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
    t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
  
  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
  
  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
  
  val elements : 'a1 t -> 'a1 t
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
  | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
     * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
  
  val coq_R_fold_rect :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
    'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
  
  val coq_R_fold_rec :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 ->
    'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
  
  val fold_rect :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3
    -> 'a2
  
  val fold_rec :
    (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
    (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3
    -> 'a2
  
  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
    coq_R_fold
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
  
  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
  
  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
    X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
    -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
    __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
  
  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
    X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t OrderedType.coq_Compare
    -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
    __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2
  
  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t
    -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t
    -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
    'a2
  
  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
    'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t
    -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1) prod
    list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t
    -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
    'a2
  
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
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key, 'a3)
    prod list
  
  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option
  
  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
 end

module Make : 
 functor (X:OrderedType.OrderedType) ->
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
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
    
    val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2
    
    val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
    val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
    val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
    
    val find : key -> 'a1 t -> 'a1 option
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt t
    | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
    | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
    | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
       * 'elt coq_R_find
    
    val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2
    
    val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
    val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
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
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add ->
      'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
    
    val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add ->
      'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2
    
    val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
      'a2
    
    val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
      'a2
    
    val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
    
    val remove : key -> 'a1 t -> 'a1 t
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt t
    | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
    | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
    | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
       * 'elt coq_R_remove
    
    val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
    
    val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2
    
    val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
    val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
    
    val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
    
    val elements : 'a1 t -> 'a1 t
    
    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
    
    type ('elt, 'a) coq_R_fold =
    | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
    | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
       * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
    
    val coq_R_fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key ->
      'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold ->
      'a2
    
    val coq_R_fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key ->
      'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold ->
      'a2
    
    val fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
      -> 'a3 -> 'a2
    
    val fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
      -> 'a3 -> 'a2
    
    val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold
    
    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
    
    type 'elt coq_R_equal =
    | R_equal_0 of 'elt t * 'elt t
    | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
       X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
    | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
       X.t * 'elt * (X.t, 'elt) prod list * X.t OrderedType.coq_Compare
    | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
    
    val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
      'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
      __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
      OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
      coq_R_equal -> 'a2
    
    val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
      'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
      __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t
      OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
      coq_R_equal -> 'a2
    
    val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
      t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2)
      -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a2
    
    val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
      t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> X.t OrderedType.coq_Compare -> __ -> __ -> 'a2)
      -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a2
    
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
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option
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

