open Alphabet
open Datatypes
open Grammar
open List0
open Specif
open Tuples

type __ = Obj.t

module type AutInit = 
 sig 
  module Gram : 
   T
  
  type noninitstate 
  
  val coq_NonInitStateAlph : noninitstate coq_Alphabet
  
  val last_symb_of_non_init_state : noninitstate -> Gram.symbol
 end

module Types : 
 functor (Init:AutInit) ->
 sig 
  type state =
    | Init
    | Ninit of Init.noninitstate
  
  val state_rect : 'a1 -> (Init.noninitstate -> 'a1) -> state -> 'a1
  
  val state_rec : 'a1 -> (Init.noninitstate -> 'a1) -> state -> 'a1
  
  val coq_StateAlph : state coq_Alphabet
  
  type action =
    | Shift_act of Init.noninitstate
    | Reduce_act of Init.Gram.production
    | Fail_act
  
  val action_rect :
    Init.Gram.terminal -> (Init.noninitstate -> __ -> 'a1) ->
    (Init.Gram.production -> 'a1) -> 'a1 -> action -> 'a1
  
  val action_rec :
    Init.Gram.terminal -> (Init.noninitstate -> __ -> 'a1) ->
    (Init.Gram.production -> 'a1) -> 'a1 -> action -> 'a1
  
  type default_action =
    | Default_reduce_act of Init.Gram.production
    | Accept_act
  
  val default_action_rect :
    (Init.Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  val default_action_rec :
    (Init.Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  type pseudoprod = Init.Gram.production option
  
  type item = { pseudoprod_item : pseudoprod; dot_pos_item : 
                nat; lookaheads_item : Init.Gram.terminal list }
  
  val item_rect :
    (pseudoprod -> nat -> Init.Gram.terminal list -> 'a1) -> item -> 'a1
  
  val item_rec :
    (pseudoprod -> nat -> Init.Gram.terminal list -> 'a1) -> item -> 'a1
  
  val pseudoprod_item : item -> pseudoprod
  
  val dot_pos_item : item -> nat
  
  val lookaheads_item : item -> Init.Gram.terminal list
 end

module type T = 
 sig 
  module Gram : 
   T
  
  type noninitstate 
  
  val coq_NonInitStateAlph : noninitstate coq_Alphabet
  
  val last_symb_of_non_init_state : noninitstate -> Gram.symbol
  
  type state =
    | Init
    | Ninit of noninitstate
  
  val state_rect : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1
  
  val state_rec : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1
  
  val coq_StateAlph : state coq_Alphabet
  
  type action =
    | Shift_act of noninitstate
    | Reduce_act of Gram.production
    | Fail_act
  
  val action_rect :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> action -> 'a1
  
  val action_rec :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> action -> 'a1
  
  type default_action =
    | Default_reduce_act of Gram.production
    | Accept_act
  
  val default_action_rect :
    (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  val default_action_rec :
    (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  type pseudoprod = Gram.production option
  
  type item = { pseudoprod_item : pseudoprod; dot_pos_item : 
                nat; lookaheads_item : Gram.terminal list }
  
  val item_rect :
    (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val item_rec :
    (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val pseudoprod_item : item -> pseudoprod
  
  val dot_pos_item : item -> nat
  
  val lookaheads_item : item -> Gram.terminal list
  
  module GramDefs : 
   sig 
    type token = (Gram.terminal, Gram.symbol_semantic_type) sigT
    
    type parse_tree =
      | Terminal_pt of Gram.terminal * Gram.symbol_semantic_type
      | Non_terminal_pt of Gram.production * token list * 
         tuple * parse_tree_list
    and parse_tree_list =
      | Nil_ptl
      | Cons_ptl of token list * Gram.symbol * Gram.symbol_semantic_type
         * parse_tree * token list * Gram.symbol list * 
         tuple * parse_tree_list
    
    val parse_tree_rect :
      (Gram.terminal -> Gram.symbol_semantic_type -> 'a1) -> (Gram.production
      -> token list -> tuple -> parse_tree_list -> 'a1) -> Gram.symbol ->
      token list -> Gram.symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_rec :
      (Gram.terminal -> Gram.symbol_semantic_type -> 'a1) -> (Gram.production
      -> token list -> tuple -> parse_tree_list -> 'a1) -> Gram.symbol ->
      token list -> Gram.symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_list_rect :
      'a1 -> (token list -> Gram.symbol -> Gram.symbol_semantic_type ->
      parse_tree -> token list -> Gram.symbol list -> tuple ->
      parse_tree_list -> 'a1 -> 'a1) -> Gram.symbol list -> token list ->
      tuple -> parse_tree_list -> 'a1
    
    val parse_tree_list_rec :
      'a1 -> (token list -> Gram.symbol -> Gram.symbol_semantic_type ->
      parse_tree -> token list -> Gram.symbol list -> tuple ->
      parse_tree_list -> 'a1 -> 'a1) -> Gram.symbol list -> token list ->
      tuple -> parse_tree_list -> 'a1
    
    val parse_tree_size :
      Gram.symbol -> token list -> Gram.symbol_semantic_type -> parse_tree ->
      nat
    
    val parse_tree_list_size :
      Gram.symbol list -> token list -> tuple -> parse_tree_list -> nat
   end
  
  val action_table : state -> (default_action, Gram.terminal -> action) sum
  
  val goto_table : state -> Gram.nonterminal -> noninitstate option
  
  val past_symb_of_non_init_state : noninitstate -> Gram.symbol list
  
  val past_state_of_non_init_state : noninitstate -> (state -> bool) list
  
  val items_of_state : state -> item list
  
  val nullable_nterm : Gram.nonterminal -> bool
  
  val first_nterm : Gram.nonterminal -> Gram.terminal list
 end

