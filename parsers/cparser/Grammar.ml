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

module Symbol = 
 functor (A:Alphs) ->
 struct 
  type symbol =
  | T of A.terminal
  | NT of A.nonterminal
  
  (** val symbol_rect :
      (A.terminal -> 'a1) -> (A.nonterminal -> 'a1) -> symbol -> 'a1 **)
  
  let symbol_rect f f0 = function
  | T x -> f x
  | NT x -> f0 x
  
  (** val symbol_rec :
      (A.terminal -> 'a1) -> (A.nonterminal -> 'a1) -> symbol -> 'a1 **)
  
  let symbol_rec f f0 = function
  | T x -> f x
  | NT x -> f0 x
  
  (** val coq_SymbolAlph : symbol coq_Alphabet **)
  
  let coq_SymbolAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | T x0 ->
        (match y with
         | T y0 -> compare A.coq_TerminalAlph.coq_AlphabetComparable x0 y0
         | NT n -> Gt)
      | NT x0 ->
        (match y with
         | T t -> Lt
         | NT y0 ->
           compare A.coq_NonTerminalAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app
        (map (fun x -> T x) (all_list A.coq_TerminalAlph.coq_AlphabetFinite))
        (map (fun x -> NT x)
          (all_list A.coq_NonTerminalAlph.coq_AlphabetFinite))) }
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

module Defs = 
 functor (G:T) ->
 struct 
  type token = (G.terminal, G.symbol_semantic_type) sigT
  
  type parse_tree =
  | Terminal_pt of G.terminal * G.symbol_semantic_type
  | Non_terminal_pt of G.production * token list * tuple * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of token list * G.symbol * G.symbol_semantic_type * parse_tree
     * token list * G.symbol list * tuple * parse_tree_list
  
  (** val parse_tree_rect :
      (G.terminal -> G.symbol_semantic_type -> 'a1) -> (G.production -> token
      list -> tuple -> parse_tree_list -> 'a1) -> G.symbol -> token list ->
      G.symbol_semantic_type -> parse_tree -> 'a1 **)
  
  let parse_tree_rect f f0 head_symbol word semantic_value = function
  | Terminal_pt (x, x0) -> f x x0
  | Non_terminal_pt (x, x0, x1, x2) -> f0 x x0 x1 x2
  
  (** val parse_tree_rec :
      (G.terminal -> G.symbol_semantic_type -> 'a1) -> (G.production -> token
      list -> tuple -> parse_tree_list -> 'a1) -> G.symbol -> token list ->
      G.symbol_semantic_type -> parse_tree -> 'a1 **)
  
  let parse_tree_rec f f0 head_symbol word semantic_value = function
  | Terminal_pt (x, x0) -> f x x0
  | Non_terminal_pt (x, x0, x1, x2) -> f0 x x0 x1 x2
  
  (** val parse_tree_list_rect :
      'a1 -> (token list -> G.symbol -> G.symbol_semantic_type -> parse_tree
      -> token list -> G.symbol list -> tuple -> parse_tree_list -> 'a1 ->
      'a1) -> G.symbol list -> token list -> tuple -> parse_tree_list -> 'a1 **)
  
  let rec parse_tree_list_rect f f0 head_symbols word semantic_values = function
  | Nil_ptl -> f
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, p0, wordq, head_symbolsq,
       semantic_valuesq, p1) ->
    f0 wordt head_symbolt semantic_valuet p0 wordq head_symbolsq
      semantic_valuesq p1
      (parse_tree_list_rect f f0 head_symbolsq wordq semantic_valuesq p1)
  
  (** val parse_tree_list_rec :
      'a1 -> (token list -> G.symbol -> G.symbol_semantic_type -> parse_tree
      -> token list -> G.symbol list -> tuple -> parse_tree_list -> 'a1 ->
      'a1) -> G.symbol list -> token list -> tuple -> parse_tree_list -> 'a1 **)
  
  let rec parse_tree_list_rec f f0 head_symbols word semantic_values = function
  | Nil_ptl -> f
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, p0, wordq, head_symbolsq,
       semantic_valuesq, p1) ->
    f0 wordt head_symbolt semantic_valuet p0 wordq head_symbolsq
      semantic_valuesq p1
      (parse_tree_list_rec f f0 head_symbolsq wordq semantic_valuesq p1)
  
  (** val parse_tree_size :
      G.symbol -> token list -> G.symbol_semantic_type -> parse_tree -> nat **)
  
  let rec parse_tree_size head_symbol word sem = function
  | Terminal_pt (t, sem0) -> O
  | Non_terminal_pt (p, word0, semantic_values, l) ->
    parse_tree_list_size (G.prod_rhs p) word0 semantic_values l
  
  (** val parse_tree_list_size :
      G.symbol list -> token list -> tuple -> parse_tree_list -> nat **)
  
  and parse_tree_list_size head_symbols word sems = function
  | Nil_ptl -> O
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, t, wordq, head_symbolsq,
       semantic_valuesq, q) ->
    plus (parse_tree_size head_symbolt wordt semantic_valuet t) (S
      (parse_tree_list_size head_symbolsq wordq semantic_valuesq q))
 end

