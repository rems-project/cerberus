open Alphabet
open Automaton
open Datatypes
open FMapAVL
open FSetAVL
open Int0
open List0

type __ = Obj.t

module Make = 
 functor (A:T) ->
 struct 
  module TerminalComparableM = 
   struct 
    type t = A.Gram.terminal
    
    (** val tComparable : t coq_Comparable **)
    
    let tComparable =
      A.Gram.coq_TerminalAlph.coq_AlphabetComparable
   end
  
  module TerminalOrderedType = OrderedType_from_ComparableM(TerminalComparableM)
  
  module StatePseudoprodPosComparableM = 
   struct 
    type t = (A.state*A.pseudoprod)*nat
    
    (** val tComparable : t coq_Comparable **)
    
    let tComparable =
      coq_PairComparable
        (coq_PairComparable A.coq_StateAlph.coq_AlphabetComparable
          (coq_OptionComparable
            A.Gram.coq_ProductionAlph.coq_AlphabetComparable)) natComparable
   end
  
  module StatePseudoprodPosOrderedType = OrderedType_from_ComparableM(StatePseudoprodPosComparableM)
  
  module TerminalSet = Make(TerminalOrderedType)
  
  module StatePseudoprodPosMap = FMapAVL.Make(StatePseudoprodPosOrderedType)
  
  (** val pseudoprod_rhs : A.Gram.production option -> A.Gram.symbol list **)
  
  let pseudoprod_rhs = function
  | Some prod -> A.Gram.prod_rhs prod
  | None -> A.Gram.start_symbol::[]
  
  (** val nullable_symb : A.Gram.symbol -> bool **)
  
  let nullable_symb = function
  | A.Gram.T t0 -> false
  | A.Gram.NT nt -> A.nullable_nterm nt
  
  (** val nullable_word : A.Gram.symbol list -> bool **)
  
  let nullable_word word =
    forallb nullable_symb word
  
  (** val first_nterm_set : A.Gram.nonterminal -> TerminalSet.t **)
  
  let first_nterm_set nterm =
    fold_left (fun acc t0 -> TerminalSet.add t0 acc) (A.first_nterm nterm)
      TerminalSet.empty
  
  (** val first_symb_set : A.Gram.symbol -> TerminalSet.t **)
  
  let first_symb_set = function
  | A.Gram.T t0 -> TerminalSet.singleton t0
  | A.Gram.NT nt -> first_nterm_set nt
  
  (** val first_word_set : A.Gram.symbol list -> TerminalSet.t **)
  
  let rec first_word_set = function
  | [] -> TerminalSet.empty
  | t0::q ->
    if nullable_symb t0
    then TerminalSet.union (first_symb_set t0) (first_word_set q)
    else first_symb_set t0
  
  (** val future_of_pseudoprod :
      A.Gram.production option -> nat -> A.Gram.symbol list **)
  
  let future_of_pseudoprod pseudoprod0 dot_pos =
    let rec loop n lst =
      match n with
      | O -> lst
      | S x ->
        (match loop x lst with
         | [] -> []
         | y::q -> q)
    in loop dot_pos (pseudoprod_rhs pseudoprod0)
  
  (** val items_map : TerminalSet.t StatePseudoprodPosMap.t **)
  
  let items_map =
    fold_left (fun acc state0 ->
      fold_left (fun acc0 item ->
        let key0 = (state0,(A.pseudoprod_item item)),(A.dot_pos_item item) in
        let data =
          fold_left (fun acc1 t0 -> TerminalSet.add t0 acc1)
            (A.lookaheads_item item) TerminalSet.empty
        in
        let old =
          match StatePseudoprodPosMap.find key0 acc0 with
          | Some x -> x
          | None -> TerminalSet.empty
        in
        StatePseudoprodPosMap.add key0 (TerminalSet.union data old) acc0)
        (A.items_of_state state0) acc)
      (all_list A.coq_StateAlph.coq_AlphabetFinite)
      StatePseudoprodPosMap.empty
  
  (** val find_items_map :
      A.state -> A.pseudoprod -> nat -> TerminalSet.t **)
  
  let find_items_map state0 pseudoprod0 dot_pos =
    match StatePseudoprodPosMap.find ((state0,pseudoprod0),dot_pos) items_map with
    | Some x -> x
    | None -> TerminalSet.empty
  
  (** val forallb_items :
      (A.state -> A.pseudoprod -> nat -> TerminalSet.t -> bool) -> bool **)
  
  let forallb_items p =
    StatePseudoprodPosMap.fold (fun key0 set acc ->
      let p0,pos = key0 in
      let st,mp = p0 in if acc then p st mp pos set else false) items_map
      true
  
  (** val is_nullable_stable : bool **)
  
  let is_nullable_stable =
    forallb (fun p ->
      implb (nullable_word (A.Gram.prod_rhs p))
        (A.nullable_nterm (A.Gram.prod_lhs p)))
      (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)
  
  (** val is_first_stable : bool **)
  
  let is_first_stable =
    forallb (fun p ->
      TerminalSet.subset (first_word_set (A.Gram.prod_rhs p))
        (first_nterm_set (A.Gram.prod_lhs p)))
      (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)
  
  (** val is_end_accept : bool **)
  
  let is_end_accept =
    forallb_items (fun st mp pos lset ->
      match mp with
      | Some p -> true
      | None ->
        (match future_of_pseudoprod None pos with
         | [] ->
           (match A.action_table st with
            | Coq_inl d ->
              (match d with
               | A.Default_reduce_act p -> false
               | A.Accept_act -> true)
            | Coq_inr a -> false)
         | s::l -> true))
  
  (** val is_start_future : bool **)
  
  let is_start_future =
    forallb (fun t0 -> TerminalSet.mem t0 (find_items_map A.Init None O))
      (all_list A.Gram.coq_TerminalAlph.coq_AlphabetFinite)
  
  (** val is_terminal_shift : bool **)
  
  let is_terminal_shift =
    forallb_items (fun s1 mp pos lset ->
      match future_of_pseudoprod mp pos with
      | [] -> true
      | s::l ->
        (match s with
         | A.Gram.T t0 ->
           (match A.action_table s1 with
            | Coq_inl d -> false
            | Coq_inr awp ->
              (match awp t0 with
               | A.Shift_act s2 ->
                 TerminalSet.subset lset
                   (find_items_map (A.Ninit s2) mp (S pos))
               | _ -> false))
         | A.Gram.NT n -> true))
  
  (** val is_end_reduce : bool **)
  
  let is_end_reduce =
    forallb_items (fun s mp pos lset ->
      match future_of_pseudoprod mp pos with
      | [] ->
        (match mp with
         | Some p1 ->
           (match A.action_table s with
            | Coq_inl d ->
              (match d with
               | A.Default_reduce_act p2 ->
                 compare_eqb A.Gram.coq_ProductionAlph.coq_AlphabetComparable
                   p1 p2
               | A.Accept_act -> false)
            | Coq_inr awt ->
              TerminalSet.fold (fun lookahead acc ->
                match awt lookahead with
                | A.Reduce_act p2 ->
                  if acc
                  then compare_eqb
                         A.Gram.coq_ProductionAlph.coq_AlphabetComparable p1
                         p2
                  else false
                | _ -> false) lset true)
         | None -> true)
      | s0::l -> true)
  
  (** val is_non_terminal_goto : bool **)
  
  let is_non_terminal_goto =
    forallb_items (fun s1 mp pos lset ->
      match future_of_pseudoprod mp pos with
      | [] -> true
      | s::l ->
        (match s with
         | A.Gram.T t0 -> true
         | A.Gram.NT nt ->
           (match A.goto_table s1 nt with
            | Some s0 ->
              TerminalSet.subset lset
                (find_items_map (A.Ninit s0) mp (S pos))
            | None -> true)))
  
  (** val is_non_terminal_closed : bool **)
  
  let is_non_terminal_closed =
    forallb_items (fun s1 mp pos lset ->
      match future_of_pseudoprod mp pos with
      | [] -> true
      | s::q ->
        (match s with
         | A.Gram.T t0 -> true
         | A.Gram.NT nt ->
           forallb (fun p ->
             if compare_eqb A.Gram.coq_NonTerminalAlph.coq_AlphabetComparable
                  (A.Gram.prod_lhs p) nt
             then let lookaheads = find_items_map s1 (Some p) O in
                  if if nullable_word q
                     then TerminalSet.subset lset lookaheads
                     else true
                  then TerminalSet.subset (first_word_set q) lookaheads
                  else false
             else true)
             (all_list A.Gram.coq_ProductionAlph.coq_AlphabetFinite)))
  
  (** val is_complete : bool **)
  
  let is_complete =
    if if if if if if if is_nullable_stable then is_first_stable else false
                   then is_end_accept
                   else false
                then is_start_future
                else false
             then is_terminal_shift
             else false
          then is_end_reduce
          else false
       then is_non_terminal_goto
       else false
    then is_non_terminal_closed
    else false
 end

