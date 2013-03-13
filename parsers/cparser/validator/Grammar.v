(*
LR(1) parser validator
Copyright (C) 2011 INRIA

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>

Jacques-Henri Jourdan <jacques-henri.jourdan@ens.fr>
*)

Require Import List.
Require Import Syntax.
Require Import Alphabet.
Require Import Orders.

(** The terminal non-terminal alphabets of the grammar. **)
Module Type Alphs.
  Parameters terminal nonterminal : Type.
  Declare Instance TerminalAlph: Alphabet terminal.
  Declare Instance NonTerminalAlph: Alphabet nonterminal.
End Alphs.

(** Definition of the alphabet of symbols, given the alphabet of terminals
    and the alphabet of non terminals **)
Module Symbol(Import A:Alphs).

  Inductive symbol :=
    | T: terminal -> symbol
    | NT: nonterminal -> symbol.

  Program Instance SymbolAlph : Alphabet symbol :=
    { AlphabetComparable := {| compare := fun x y =>
        match x, y return comparison with
          | T _, NT _ => Gt
          | NT _, T _ => Lt
          | T x, T y => compare x y
          | NT x, NT y => compare x y
        end |};
      AlphabetFinite := {| all_list :=
        map T all_list++map NT all_list |} }.
  Next Obligation.
  destruct x; destruct y; intuition; apply compare_antisym.
  Qed.
  Next Obligation.
  destruct x; destruct y; destruct z; intuition; try discriminate.
  apply (compare_trans _ t0); intuition.
  apply (compare_trans _ n0); intuition.
  Qed.
  Next Obligation.
  intros x y.
  destruct x; destruct y; try discriminate; intros.
  rewrite (compare_eq t t0); intuition.
  rewrite (compare_eq n n0); intuition.
  Qed.
  Next Obligation.
  rewrite in_app_iff.
  destruct x; [left | right]; apply in_map; apply all_list_forall.
  Qed.

End Symbol.

Module Type T.
  Require Export Tuples.

  Include Alphs <+ Symbol.

  (** [symbol_semantic_type] maps a symbols to the type of its semantic
     values. **)
  Parameter symbol_semantic_type: symbol -> Type.

  (** The type of productions identifiers **)
  Parameter production : Type.
  Declare Instance ProductionAlph : Alphabet production.

  (** Accessors for productions: left hand side, right hand side,
     and semantic action. The semantic actions are given in the form
     of curryfied functions **)
  Parameter prod_lhs: production -> nonterminal.
  Parameter prod_rhs: production -> list symbol.
  Parameter prod_action:
    forall p:production,
      arrows
        (map symbol_semantic_type (prod_rhs p))
        (symbol_semantic_type (NT (prod_lhs p))).

  (** The start symbol. It can be either a terminal (useless) or
     a non-terminal. **)
  Parameter start_symbol: symbol.
End T.

Module Defs(Import G:T).

  (** A token is a terminal and a semantic value for this terminal. **)
  Definition token := {t:terminal & symbol_semantic_type (T t)}.

  (** A grammar creates a relation between word of tokens and semantic values.
     This relation is parametrized by the head symbol. It defines the 
     "semantics" of the grammar. This relation is defined by a notion of 
     parse tree. **)
  Inductive parse_tree:
    forall (head_symbol:symbol) (word:list token)
      (semantic_value:symbol_semantic_type head_symbol), Type :=

  (** A single token has its semantic value as semantic value, for the
     corresponding terminal as head symbol. **)
  | Terminal_pt:
    forall (t:terminal) (sem:symbol_semantic_type (T t)),
      parse_tree (T t)
      [existT (fun t => symbol_semantic_type (T t)) t sem] sem

  (** Given a production, if a word has a list of semantic values for the 
     right hand side as head symbols, then this word has the semantic value 
     given by the semantic action of the production for the left hand side 
     as head symbol.**)
  | Non_terminal_pt:
    forall (p:production) (word:list token)
      (semantic_values:tuple (map symbol_semantic_type (prod_rhs p))),
      parse_tree_list (prod_rhs p) word semantic_values ->
      parse_tree
        (NT (prod_lhs p))
        word
        (uncurry (prod_action p) semantic_values)

  (** Basically the same relation as before, but for list of head symbols (ie.
     We are building a forest of syntax trees. It is mutually recursive with the
     previous relation **)
  with parse_tree_list:
    forall (head_symbols:list symbol) (word:list token)
      (semantic_values:tuple (map symbol_semantic_type head_symbols)),
      Type :=

  (** The empty word has [()] as semantic for [[]] as head symbols list **)
  | Nil_ptl: parse_tree_list [] [] ()

  (** The cons of the semantic value for one head symbol and for a list of head
     symbols **)
  | Cons_ptl:
  (** The semantic for the head **)
    forall (wordt:list token)
      (head_symbolt:symbol)
      (semantic_valuet:symbol_semantic_type head_symbolt),
      parse_tree head_symbolt wordt semantic_valuet ->

  (** and the semantic for the tail **)
      forall (wordq:list token)
        (head_symbolsq:list symbol)
        (semantic_valuesq:tuple (map symbol_semantic_type head_symbolsq)),
        parse_tree_list head_symbolsq wordq semantic_valuesq ->

  (** give the semantic of the cons **)
        parse_tree_list
          (head_symbolt::head_symbolsq)
          (wordt++wordq)
          (semantic_valuet,semantic_valuesq).

  Definition has_semantic_value word sem : Prop :=
    inhabited (parse_tree start_symbol word sem).

  Fixpoint parse_tree_size {head_symbol word sem} (tree:parse_tree head_symbol word sem) :=
    match tree with 
      | Terminal_pt _ _ => 0
      | Non_terminal_pt _ _ _ l => parse_tree_list_size l
    end
  with parse_tree_list_size {head_symbols word sems} (tree:parse_tree_list head_symbols word sems) :=
    match tree with
      | Nil_ptl => 0
      | Cons_ptl _ _ _ t _ _ _ q =>
         parse_tree_size t+S (parse_tree_list_size q)
    end.
End Defs.
