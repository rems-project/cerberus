open Alphabet
open Automaton
open Datatypes
open Int0
open Interpreter
open Interpreter_complete
open Interpreter_correct
open Interpreter_safe
open Specif
open Streams
open Tuples

type __ = Obj.t

module Make : 
 functor (Aut:Automaton.T) ->
 sig 
  module Inter : 
   sig 
    type 'a result =
    | Err
    | OK of 'a
    
    val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
    
    val bind2 : ('a1*'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
    
    val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream
    
    type stack =
    | Nil_stack
    | Cons_stack of Aut.noninitstate * Aut.Gram.symbol_semantic_type * stack
    
    val stack_rect :
      'a1 -> (Aut.noninitstate -> Aut.Gram.symbol_semantic_type -> stack ->
      'a1 -> 'a1) -> stack -> 'a1
    
    val stack_rec :
      'a1 -> (Aut.noninitstate -> Aut.Gram.symbol_semantic_type -> stack ->
      'a1 -> 'a1) -> stack -> 'a1
    
    val state_of_stack : stack -> Aut.state
    
    val pop :
      Aut.Gram.symbol list -> stack -> Aut.Gram.symbol list -> tuple ->
      (stack*tuple) result
    
    val reduce : stack -> Aut.Gram.production -> stack result
    
    type step_result =
    | Fail_sr
    | Accept_sr of Aut.Gram.symbol_semantic_type
       * Aut.GramDefs.token coq_Stream
    | Progress_sr of stack * Aut.GramDefs.token coq_Stream
    
    val step_result_rect :
      'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token coq_Stream
      -> 'a1) -> (stack -> Aut.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1
    
    val step_result_rec :
      'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token coq_Stream
      -> 'a1) -> (stack -> Aut.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1
    
    val step : stack -> Aut.GramDefs.token coq_Stream -> step_result result
    
    type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of Aut.Gram.symbol_semantic_type
       * Aut.GramDefs.token coq_Stream
    
    val parse_result_rect :
      'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1
    
    val parse_result_rec :
      'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1
    
    val parse_fix :
      stack -> Aut.GramDefs.token coq_Stream -> nat -> parse_result result
    
    val parse : Aut.GramDefs.token coq_Stream -> nat -> parse_result result
   end
  
  module Safe : 
   sig 
    module Valid : 
     sig 
      val singleton_state_pred : Aut.state -> Aut.state -> bool
      
      val past_state_of_state : Aut.state -> (Aut.state -> bool) list
      
      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list
      
      val head_states_of_state : Aut.state -> (Aut.state -> bool) list
      
      val is_initial_no_accept : bool
      
      val is_accept_last_symb : bool
      
      val is_accept_initial : bool
      
      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool
      
      val is_shift_head_symbs : bool
      
      val is_goto_head_symbs : bool
      
      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool
      
      val is_shift_past_state : bool
      
      val is_goto_past_state : bool
      
      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool
      
      val is_valid_for_reduce : Aut.state -> Aut.Gram.production -> bool
      
      val is_reduce_ok : bool
      
      val is_safe : bool
     end
    
    val symb_stack_of_stack : Inter.stack -> Aut.Gram.symbol list
    
    val state_stack_of_stack : Inter.stack -> (Aut.state -> bool) list
    
    val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
    
    val parse_with_safe :
      Aut.GramDefs.token coq_Stream -> nat -> Inter.parse_result
   end
  
  module Correct : 
   sig 
    val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
   end
  
  module Complete : 
   sig 
    module Valid : 
     sig 
      module TerminalComparableM : 
       sig 
        type t = Aut.Gram.terminal
        
        val tComparable : t coq_Comparable
       end
      
      module TerminalOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = TerminalComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
        
        val eq_dec : Alt.t -> Alt.t -> bool
       end
      
      module StatePseudoprodPosComparableM : 
       sig 
        type t = (Aut.state*Aut.pseudoprod)*nat
        
        val tComparable : t coq_Comparable
       end
      
      module StatePseudoprodPosOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = StatePseudoprodPosComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
        
        val eq_dec : Alt.t -> Alt.t -> bool
       end
      
      module TerminalSet : 
       sig 
        module X' : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end
        
        module MSet : 
         sig 
          module Raw : 
           sig 
            type elt = TerminalOrderedType.Alt.t
            
            type tree =
            | Leaf
            | Node of tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            
            type t = tree
            
            val height : t -> Z_as_Int.int
            
            val cardinal : t -> nat
            
            val empty : tree
            
            val is_empty : tree -> bool
            
            val mem : TerminalOrderedType.Alt.t -> tree -> bool
            
            val singleton : TerminalOrderedType.Alt.t -> tree
            
            val create : tree -> TerminalOrderedType.Alt.t -> tree -> tree
            
            val assert_false :
              tree -> TerminalOrderedType.Alt.t -> tree -> tree
            
            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
            
            val add : TerminalOrderedType.Alt.t -> tree -> tree
            
            val join : tree -> elt -> t -> t
            
            val remove_min : tree -> elt -> t -> t*elt
            
            val merge : tree -> tree -> tree
            
            val remove : TerminalOrderedType.Alt.t -> tree -> tree
            
            val min_elt : tree -> TerminalOrderedType.Alt.t option
            
            val max_elt : tree -> TerminalOrderedType.Alt.t option
            
            val choose : tree -> TerminalOrderedType.Alt.t option
            
            val concat : tree -> tree -> tree
            
            type triple = { t_left : t; t_in : bool; t_right : t }
            
            val t_left : triple -> t
            
            val t_in : triple -> bool
            
            val t_right : triple -> t
            
            val split : TerminalOrderedType.Alt.t -> tree -> triple
            
            val inter : tree -> tree -> tree
            
            val diff : tree -> tree -> tree
            
            val union : tree -> tree -> tree
            
            val elements_aux :
              TerminalOrderedType.Alt.t list -> t ->
              TerminalOrderedType.Alt.t list
            
            val elements : t -> TerminalOrderedType.Alt.t list
            
            val filter_acc : (elt -> bool) -> tree -> tree -> tree
            
            val filter : (elt -> bool) -> tree -> tree
            
            val partition_acc : (elt -> bool) -> (t*t) -> t -> t*t
            
            val partition : (elt -> bool) -> t -> t*t
            
            val for_all : (elt -> bool) -> tree -> bool
            
            val exists_ : (elt -> bool) -> tree -> bool
            
            val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
            
            val subsetl :
              (t -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subsetr :
              (t -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subset : tree -> tree -> bool
            
            type enumeration =
            | End
            | More of elt * t * enumeration
            
            val cons : tree -> enumeration -> enumeration
            
            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison
            
            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration ->
              comparison
            
            val compare_end : enumeration -> comparison
            
            val compare : tree -> tree -> comparison
            
            val equal : tree -> tree -> bool
            
            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val isok : tree -> bool
            
            module MX : 
             sig 
              module OrderTac : 
               sig 
                module OTF : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
                
                module TO : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
             end
            
            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t
            
            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * (t*elt)
               * coq_R_remove_min * t * elt
            
            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_merge_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * elt
            
            type coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int
            | R_min_elt_2 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * TerminalOrderedType.Alt.t option
               * coq_R_min_elt
            
            type coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int
            | R_max_elt_2 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * TerminalOrderedType.Alt.t option
               * coq_R_max_elt
            
            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_concat_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * elt
            
            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_inter_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
               * tree * coq_R_inter
            | R_inter_3 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
               * tree * coq_R_inter
            
            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_diff_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff
            | R_diff_3 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff
            
            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_union_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_union
               * tree * coq_R_union
            
            module L : 
             sig 
              module MO : 
               sig 
                module OrderTac : 
                 sig 
                  module OTF : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                  
                  module TO : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                 end
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
                
                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
                
                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end
            
            val flatten_e : enumeration -> elt list
           end
          
          module E : 
           sig 
            type t = TerminalOrderedType.Alt.t
            
            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
          
          type elt = TerminalOrderedType.Alt.t
          
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
          
          val partition : (elt -> bool) -> t -> t*t
          
          val eq_dec : t -> t -> bool
          
          val compare : t -> t -> comparison
          
          val min_elt : t -> elt option
          
          val max_elt : t -> elt option
         end
        
        type elt = TerminalOrderedType.Alt.t
        
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
        
        val partition : (elt -> bool) -> t -> t*t
        
        val cardinal : t -> nat
        
        val elements : t -> elt list
        
        val choose : t -> elt option
        
        module MF : 
         sig 
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
        
        val min_elt : t -> elt option
        
        val max_elt : t -> elt option
        
        val compare : t -> t -> t OrderedType.coq_Compare
        
        module E : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t OrderedType.coq_Compare
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
       end
      
      module StatePseudoprodPosMap : 
       sig 
        module E : 
         sig 
          type t = StatePseudoprodPosOrderedType.Alt.t
          
          val compare :
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
          
          val eq_dec :
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t -> bool
         end
        
        module Raw : 
         sig 
          type key = StatePseudoprodPosOrderedType.Alt.t
          
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
          
          val mem : StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> bool
          
          val find :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
          
          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)
          
          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val remove :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
          
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
          
          val split :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
          
          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list
          
          val elements : 'a1 tree -> (key*'a1) list
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
          
          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration
          
          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
          
          val equal_more :
            ('a1 -> 'a1 -> bool) -> StatePseudoprodPosOrderedType.Alt.t ->
            'a1 -> ('a1 enumeration -> bool) -> 'a1 enumeration -> bool
          
          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool
          
          val equal_end : 'a1 enumeration -> bool
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
          
          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
          
          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree
          
          module Proofs : 
           sig 
            module MX : 
             sig 
              module OrderElts : 
               sig 
                type t = StatePseudoprodPosOrderedType.Alt.t
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
              
              val lt_dec :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
              
              val eqb :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
             end
            
            module PX : 
             sig 
              module MO : 
               sig 
                module OrderElts : 
                 sig 
                  type t = StatePseudoprodPosOrderedType.Alt.t
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val lt_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val eqb :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
               end
             end
            
            module L : 
             sig 
              module MX : 
               sig 
                module OrderElts : 
                 sig 
                  type t = StatePseudoprodPosOrderedType.Alt.t
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val lt_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val eqb :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
               end
              
              module PX : 
               sig 
                module MO : 
                 sig 
                  module OrderElts : 
                   sig 
                    type t = StatePseudoprodPosOrderedType.Alt.t
                   end
                  
                  module OrderTac : 
                   sig 
                    
                   end
                  
                  val eq_dec :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                  
                  val lt_dec :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                  
                  val eqb :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                 end
               end
              
              type key = StatePseudoprodPosOrderedType.Alt.t
              
              type 'elt t = (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              
              val empty : 'a1 t
              
              val is_empty : 'a1 t -> bool
              
              val mem : key -> 'a1 t -> bool
              
              type 'elt coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_mem_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_mem_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * bool * 'elt coq_R_mem
              
              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
                -> 'a1 coq_R_mem -> 'a2
              
              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
                -> 'a1 coq_R_mem -> 'a2
              
              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
              
              val find : key -> 'a1 t -> 'a1 option
              
              type 'elt coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_find_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_find_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt option * 'elt coq_R_find
              
              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2
              
              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2
              
              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
              
              val add : key -> 'a1 -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_add_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_add_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt t * 'elt coq_R_add
              
              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_add -> 'a2
              
              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_add -> 'a2
              
              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              
              val remove : key -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_remove_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_remove_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt t * 'elt coq_R_remove
              
              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
              
              val elements : 'a1 t -> 'a1 t
              
              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
              
              type ('elt, 'a) coq_R_fold =
              | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
              | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list * 
                 'a * ('elt, 'a) coq_R_fold
              
              val coq_R_fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val coq_R_fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold
              
              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
              
              type 'elt coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list * 
                 bool * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t
                   OrderedType.coq_Compare
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
              
              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal -> 'a2
              
              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal -> 'a2
              
              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
              
              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
              
              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal
              
              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val option_cons :
                key -> 'a1 option -> (key*'a1) list -> (key*'a1) list
              
              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
              
              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
              
              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t
              
              val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t
              
              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3
              
              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key*'a3) list
              
              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option*'a2 option) option
              
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
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
              coq_R_mem -> 'a2
            
            val coq_R_mem_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
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
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
            
            val coq_R_find_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
            
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
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
              -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
              __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
              -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
              -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
              __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
              -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_add
            
            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
              -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
              -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
               * ('elt tree*(key*'elt)) * 'elt coq_R_remove_min * 'elt tree
               * (key*'elt)
            
            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> ('a1 tree*(key*'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2)
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree*(key*'a1))
              -> 'a1 coq_R_remove_min -> 'a2
            
            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> ('a1 tree*(key*'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2)
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree*(key*'a1))
              -> 'a1 coq_R_remove_min -> 'a2
            
            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt tree * (key*'elt) * 
               key * 'elt
            
            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
              'a1 coq_R_merge -> 'a2
            
            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
              'a1 coq_R_merge -> 'a2
            
            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
            
            val coq_R_remove_rect :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
            
            val coq_R_remove_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
            
            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt tree * (key*'elt)
            
            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
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
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple
              -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
              -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
              'a2
            
            val coq_R_split_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple
              -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
              -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
              'a2
            
            type ('elt, 'elt') coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt' * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            
            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
              ('a1, 'a2) coq_R_map_option -> 'a3
            
            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
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
               * 'elt' tree * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt
            
            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.int ->
              __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
              -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree
              -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
              -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
              'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4
            
            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.int ->
              __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
              -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree
              -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
              -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
              'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4
            
            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
            
            val flatten_e : 'a1 enumeration -> (key*'a1) list
           end
         end
        
        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)
        
        val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val this : 'a1 bst -> 'a1 Raw.tree
        
        type 'elt t = 'elt bst
        
        type key = StatePseudoprodPosOrderedType.Alt.t
        
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
        
        val elements : 'a1 t -> (key*'a1) list
        
        val cardinal : 'a1 t -> nat
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end
      
      val pseudoprod_rhs : Aut.Gram.production option -> Aut.Gram.symbol list
      
      val nullable_symb : Aut.Gram.symbol -> bool
      
      val nullable_word : Aut.Gram.symbol list -> bool
      
      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t
      
      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t
      
      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t
      
      val future_of_pseudoprod :
        Aut.Gram.production option -> nat -> Aut.Gram.symbol list
      
      val items_map : TerminalSet.t StatePseudoprodPosMap.t
      
      val find_items_map :
        Aut.state -> Aut.pseudoprod -> nat -> TerminalSet.t
      
      val forallb_items :
        (Aut.state -> Aut.pseudoprod -> nat -> TerminalSet.t -> bool) -> bool
      
      val is_nullable_stable : bool
      
      val is_first_stable : bool
      
      val is_end_accept : bool
      
      val is_start_future : bool
      
      val is_terminal_shift : bool
      
      val is_end_reduce : bool
      
      val is_non_terminal_goto : bool
      
      val is_non_terminal_closed : bool
      
      val is_complete : bool
     end
    
    val first_term_word :
      Aut.GramDefs.token list -> Aut.Gram.terminal -> Aut.Gram.terminal
    
    val extend_stack :
      Inter.stack -> Aut.noninitstate list -> __ -> Inter.stack
    
    type past_invariant = { states_pi : Aut.noninitstate list; sem_pi : tuple }
    
    val past_invariant_rect :
      (Aut.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1
    
    val past_invariant_rec :
      (Aut.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1
    
    val states_pi : past_invariant -> Aut.noninitstate list
    
    val symbl_pi : past_invariant -> Aut.Gram.symbol list
    
    val sem_pi : past_invariant -> tuple
    
    val stack_pi : past_invariant -> Inter.stack -> Inter.stack
    
    type hole_future_invariant = { future_hfi : (Aut.Gram.symbol list, tuple)
                                                sigT;
                                   word_future_hfi : Aut.GramDefs.token list;
                                   future_sem_proof_hfi : Aut.GramDefs.parse_tree_list;
                                   hole_hfi : (Aut.Gram.production, tuple)
                                              sigT option }
    
    val hole_future_invariant_rect :
      bool -> ((Aut.Gram.symbol list, tuple) sigT -> __ -> Aut.GramDefs.token
      list -> Aut.GramDefs.parse_tree_list -> (Aut.Gram.production, tuple)
      sigT option -> 'a1) -> hole_future_invariant -> 'a1
    
    val hole_future_invariant_rec :
      bool -> ((Aut.Gram.symbol list, tuple) sigT -> __ -> Aut.GramDefs.token
      list -> Aut.GramDefs.parse_tree_list -> (Aut.Gram.production, tuple)
      sigT option -> 'a1) -> hole_future_invariant -> 'a1
    
    val future_hfi :
      bool
      ->
      hole_future_invariant
      ->
      (Aut.Gram.symbol
      list,
      tuple)
      sigT
    
    val word_future_hfi :
      bool
      ->
      hole_future_invariant
      ->
      Aut.GramDefs.token
      list
    
    val future_sem_proof_hfi :
      bool
      ->
      hole_future_invariant
      ->
      Aut.GramDefs.parse_tree_list
    
    val hole_hfi :
      bool
      ->
      hole_future_invariant
      ->
      (Aut.Gram.production,
      tuple)
      sigT
      option
    
    val hole_pseudo_hfi :
      bool
      ->
      hole_future_invariant
      ->
      (Aut.Gram.production
      option,
      tuple)
      sigT
      option
    
    val symbl_hfi :
      bool
      ->
      hole_future_invariant
      ->
      Aut.Gram.symbol
      list
    
    val sem_hfi :
      bool
      ->
      hole_future_invariant
      ->
      tuple
    
    val coq_JMeq_rew_r :
      'a1
      ->
      'a2
      ->
      'a3
      ->
      'a3
    
    val eq_rew_r_dep :
      'a1
      ->
      'a1
      ->
      'a2
      ->
      'a2
    
    val eq_rew_dep :
      'a1
      ->
      'a2
      ->
      'a1
      ->
      'a2
   end
  
  val complete_validator :
    bool
  
  val safe_validator :
    bool
  
  val parse :
    nat
    ->
    Aut.GramDefs.token
    coq_Stream
    ->
    Inter.parse_result
 end

