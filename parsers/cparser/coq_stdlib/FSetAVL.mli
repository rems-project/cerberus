open Datatypes
open Int0
open MSetAVL
open OrdersAlt

module IntMake : 
 functor (I:Int) ->
 functor (X:OrderedType.OrderedType) ->
 sig 
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
    
    val compare : X.t -> X.t -> comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type tree =
      | Leaf
      | Node of tree * X.t * tree * I.int
      
      type t = tree
      
      val height : t -> I.int
      
      val cardinal : t -> nat
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : X.t -> tree -> bool
      
      val singleton : X.t -> tree
      
      val create : tree -> X.t -> tree -> tree
      
      val assert_false : tree -> X.t -> tree -> tree
      
      val bal : t -> X.t -> t -> tree
      
      val add : X.t -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> (t, elt) prod
      
      val merge : tree -> tree -> tree
      
      val remove : X.t -> tree -> tree
      
      val min_elt : tree -> X.t option
      
      val max_elt : tree -> X.t option
      
      val choose : tree -> X.t option
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : X.t -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val elements_aux : X.t list -> t -> X.t list
      
      val elements : t -> X.t list
      
      val filter_acc : (elt -> bool) -> tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition_acc : (elt -> bool) -> (t, t) prod -> t -> (t, t) prod
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val for_all : (elt -> bool) -> tree -> bool
      
      val exists_ : (elt -> bool) -> tree -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val subsetl : (t -> bool) -> X.t -> tree -> bool
      
      val subsetr : (t -> bool) -> X.t -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type enumeration =
      | End
      | More of elt * t * enumeration
      
      val cons : tree -> enumeration -> enumeration
      
      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_end : enumeration -> comparison
      
      val compare : tree -> tree -> comparison
      
      val equal : tree -> tree -> bool
      
      val ltb_tree : X.t -> tree -> bool
      
      val gtb_tree : X.t -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> bool
           end
          
          module TO : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> bool
           end
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * tree * X.t * tree * I.int
      | R_bal_2 of t * X.t * t * tree * X.t * tree * I.int
      | R_bal_3 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t
         * tree * I.int
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * tree * X.t * tree * I.int
      | R_bal_6 of t * X.t * t * tree * X.t * tree * I.int
      | R_bal_7 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t
         * tree * I.int
      | R_bal_8 of t * X.t * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * tree * X.t * tree * I.int
         * (t, elt) prod * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * tree * X.t * tree * I.int
      | R_merge_2 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * elt
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * tree * X.t * tree * I.int
      | R_min_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * 
         tree * I.int * X.t option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * tree * X.t * tree * I.int
      | R_max_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * 
         tree * I.int * X.t option * coq_R_max_elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * tree * X.t * tree * I.int
      | R_concat_2 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * tree * X.t * tree * I.int
      | R_inter_2 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * bool * t * tree * coq_R_inter * tree
         * coq_R_inter
      | R_inter_3 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * bool * t * tree * coq_R_inter * tree
         * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * tree * X.t * tree * I.int
      | R_diff_2 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff
      | R_diff_3 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * bool * t * tree * coq_R_diff * tree
         * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * tree * X.t * tree * I.int
      | R_union_2 of tree * tree * tree * X.t * tree * I.int * tree * 
         X.t * tree * I.int * t * bool * t * tree * coq_R_union * tree
         * coq_R_union
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> bool
             end
            
            module TO : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> bool
             end
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
     end
    
    module E : 
     sig 
      type t = X.t
      
      val compare : X.t -> X.t -> comparison
      
      val eq_dec : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val eq_dec : t -> t -> bool
    
    val compare : t -> t -> comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = X.t
  
  type t = MSet.t
  
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
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
 end

module Make : 
 functor (X:OrderedType.OrderedType) ->
 sig 
  module X' : 
   sig 
    type t = X.t
    
    val eq_dec : t -> t -> bool
    
    val compare : X.t -> X.t -> comparison
   end
  
  module MSet : 
   sig 
    module Raw : 
     sig 
      type elt = X.t
      
      type tree =
      | Leaf
      | Node of tree * X.t * tree * Z_as_Int.int
      
      type t = tree
      
      val height : t -> Z_as_Int.int
      
      val cardinal : t -> nat
      
      val empty : tree
      
      val is_empty : tree -> bool
      
      val mem : X.t -> tree -> bool
      
      val singleton : X.t -> tree
      
      val create : tree -> X.t -> tree -> tree
      
      val assert_false : tree -> X.t -> tree -> tree
      
      val bal : t -> X.t -> t -> tree
      
      val add : X.t -> tree -> tree
      
      val join : tree -> elt -> t -> t
      
      val remove_min : tree -> elt -> t -> (t, elt) prod
      
      val merge : tree -> tree -> tree
      
      val remove : X.t -> tree -> tree
      
      val min_elt : tree -> X.t option
      
      val max_elt : tree -> X.t option
      
      val choose : tree -> X.t option
      
      val concat : tree -> tree -> tree
      
      type triple = { t_left : t; t_in : bool; t_right : t }
      
      val t_left : triple -> t
      
      val t_in : triple -> bool
      
      val t_right : triple -> t
      
      val split : X.t -> tree -> triple
      
      val inter : tree -> tree -> tree
      
      val diff : tree -> tree -> tree
      
      val union : tree -> tree -> tree
      
      val elements_aux : X.t list -> t -> X.t list
      
      val elements : t -> X.t list
      
      val filter_acc : (elt -> bool) -> tree -> tree -> tree
      
      val filter : (elt -> bool) -> tree -> tree
      
      val partition_acc : (elt -> bool) -> (t, t) prod -> t -> (t, t) prod
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val for_all : (elt -> bool) -> tree -> bool
      
      val exists_ : (elt -> bool) -> tree -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val subsetl : (t -> bool) -> X.t -> tree -> bool
      
      val subsetr : (t -> bool) -> X.t -> tree -> bool
      
      val subset : tree -> tree -> bool
      
      type enumeration =
      | End
      | More of elt * t * enumeration
      
      val cons : tree -> enumeration -> enumeration
      
      val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison
      
      val compare_end : enumeration -> comparison
      
      val compare : tree -> tree -> comparison
      
      val equal : tree -> tree -> bool
      
      val ltb_tree : X.t -> tree -> bool
      
      val gtb_tree : X.t -> tree -> bool
      
      val isok : tree -> bool
      
      module MX : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> bool
           end
          
          module TO : 
           sig 
            type t = X.t
            
            val compare : X.t -> X.t -> comparison
            
            val eq_dec : X.t -> X.t -> bool
           end
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
      
      type coq_R_bal =
      | R_bal_0 of t * X.t * t
      | R_bal_1 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
      | R_bal_2 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
      | R_bal_3 of t * X.t * t * tree * X.t * tree * Z_as_Int.int * tree
         * X.t * tree * Z_as_Int.int
      | R_bal_4 of t * X.t * t
      | R_bal_5 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
      | R_bal_6 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
      | R_bal_7 of t * X.t * t * tree * X.t * tree * Z_as_Int.int * tree
         * X.t * tree * Z_as_Int.int
      | R_bal_8 of t * X.t * t
      
      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * tree * X.t * tree * Z_as_Int.int
         * (t, elt) prod * coq_R_remove_min * t * elt
      
      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
      | R_merge_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * elt
      
      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * tree * X.t * tree * Z_as_Int.int
      | R_min_elt_2 of tree * tree * X.t * tree * Z_as_Int.int * tree * 
         X.t * tree * Z_as_Int.int * X.t option * coq_R_min_elt
      
      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * tree * X.t * tree * Z_as_Int.int
      | R_max_elt_2 of tree * tree * X.t * tree * Z_as_Int.int * tree * 
         X.t * tree * Z_as_Int.int * X.t option * coq_R_max_elt
      
      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
      | R_concat_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * elt
      
      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
      | R_inter_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter
      | R_inter_3 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
         * tree * coq_R_inter
      
      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
      | R_diff_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
         * tree * coq_R_diff
      | R_diff_3 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
         * tree * coq_R_diff
      
      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
      | R_union_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
         tree * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_union
         * tree * coq_R_union
      
      module L : 
       sig 
        module MO : 
         sig 
          module OrderTac : 
           sig 
            module OTF : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> bool
             end
            
            module TO : 
             sig 
              type t = X.t
              
              val compare : X.t -> X.t -> comparison
              
              val eq_dec : X.t -> X.t -> bool
             end
           end
          
          val eq_dec : X.t -> X.t -> bool
          
          val lt_dec : X.t -> X.t -> bool
          
          val eqb : X.t -> X.t -> bool
         end
       end
      
      val flatten_e : enumeration -> elt list
     end
    
    module E : 
     sig 
      type t = X.t
      
      val compare : X.t -> X.t -> comparison
      
      val eq_dec : X.t -> X.t -> bool
     end
    
    type elt = X.t
    
    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)
    
    val this : t_ -> Raw.t
    
    type t = t_
    
    val mem : elt -> t -> bool
    
    val add : elt -> t -> t
    
    val remove : elt -> t -> t
    
    val singleton : elt -> t
    
    val union : t -> t -> t
    
    val inter : t -> t -> t
    
    val diff : t -> t -> t
    
    val equal : t -> t -> bool
    
    val subset : t -> t -> bool
    
    val empty : t
    
    val is_empty : t -> bool
    
    val elements : t -> elt list
    
    val choose : t -> elt option
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val cardinal : t -> nat
    
    val filter : (elt -> bool) -> t -> t
    
    val for_all : (elt -> bool) -> t -> bool
    
    val exists_ : (elt -> bool) -> t -> bool
    
    val partition : (elt -> bool) -> t -> (t, t) prod
    
    val eq_dec : t -> t -> bool
    
    val compare : t -> t -> comparison
    
    val min_elt : t -> elt option
    
    val max_elt : t -> elt option
   end
  
  type elt = X.t
  
  type t = MSet.t
  
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
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  module MF : 
   sig 
    val eqb : X.t -> X.t -> bool
   end
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
  
  val compare : t -> t -> t OrderedType.coq_Compare
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> t OrderedType.coq_Compare
    
    val eq_dec : t -> t -> bool
   end
 end

