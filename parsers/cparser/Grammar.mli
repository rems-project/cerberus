open Alphabet
open Datatypes
open List0
open Peano
open Specif
open Tuples

module type Alphs = 
 sig 
  type terminal 
  
  type nonterminal 
  
  val coq_TerminalAlph : terminal coq_Alphabet
  
  val coq_NonTerminalAlph : nonterminal coq_Alphabet
 end

module Symbol : 
 functor (A:Alphs) ->
 sig 
  type symbol =
  | T of A.terminal
  | NT of A.nonterminal
  
  val symbol_rect :
    (A.terminal -> 'a1) -> (A.nonterminal -> 'a1) -> symbol -> 'a1
  
  val symbol_rec :
    (A.terminal -> 'a1) -> (A.nonterminal -> 'a1) -> symbol -> 'a1
  
  val coq_SymbolAlph : symbol coq_Alphabet
 end

module type T = 
 sig 
  type terminal 
  
  type nonterminal 
  
  val coq_TerminalAlph : terminal coq_Alphabet
  
  val coq_NonTerminalAlph : nonterminal coq_Alphabet
  
  type symbol =
  | T of terminal
  | NT of nonterminal
  
  val symbol_rect :
    (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val coq_SymbolAlph : symbol coq_Alphabet
  
  type symbol_semantic_type 
  
  type production 
  
  val coq_ProductionAlph : production coq_Alphabet
  
  val prod_lhs : production -> nonterminal
  
  val prod_rhs : production -> symbol list
  
  val prod_action : production -> symbol_semantic_type arrows
  
  val start_symbol : symbol
 end

module Defs : 
 functor (G:T) ->
 sig 
  type token = (G.terminal, G.symbol_semantic_type) sigT
  
  type parse_tree =
  | Terminal_pt of G.terminal * G.symbol_semantic_type
  | Non_terminal_pt of G.production * token list * tuple * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of token list * G.symbol * G.symbol_semantic_type * parse_tree
     * token list * G.symbol list * tuple * parse_tree_list
  
  val parse_tree_rect :
    (G.terminal -> G.symbol_semantic_type -> 'a1) -> (G.production -> token
    list -> tuple -> parse_tree_list -> 'a1) -> G.symbol -> token list ->
    G.symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_rec :
    (G.terminal -> G.symbol_semantic_type -> 'a1) -> (G.production -> token
    list -> tuple -> parse_tree_list -> 'a1) -> G.symbol -> token list ->
    G.symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_list_rect :
    'a1 -> (token list -> G.symbol -> G.symbol_semantic_type -> parse_tree ->
    token list -> G.symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    G.symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_list_rec :
    'a1 -> (token list -> G.symbol -> G.symbol_semantic_type -> parse_tree ->
    token list -> G.symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    G.symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_size :
    G.symbol -> token list -> G.symbol_semantic_type -> parse_tree -> nat
  
  val parse_tree_list_size :
    G.symbol list -> token list -> tuple -> parse_tree_list -> nat
 end

