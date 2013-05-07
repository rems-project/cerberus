open Alphabet
open Automaton
open Datatypes
open List0
open Specif
open Streams
open Tuples

let __ = let rec f _ = Obj.repr f in Obj.repr f

module Make = 
 functor (A:T) ->
 struct 
  type 'a result =
    | Err
    | OK of 'a
  
  (** val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2 **)
  
  let result_rect f f0 = function
    | Err -> f
    | OK x -> f0 x
  
  (** val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2 **)
  
  let result_rec f f0 = function
    | Err -> f
    | OK x -> f0 x
  
  (** val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result **)
  
  let bind f g =
    match f with
      | Err -> Err
      | OK x -> g x
  
  (** val bind2 :
      ('a1*'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result **)
  
  let bind2 f g =
    match f with
      | Err -> Err
      | OK p -> let x,y = p in g x y
  
  (** val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream **)
  
  let rec app_str l s =
    match l with
      | [] -> s
      | t::q -> lazy (Cons (t, (app_str q s)))
  
  type stack =
    | Nil_stack
    | Cons_stack of A.noninitstate * A.Gram.symbol_semantic_type * stack
  
  (** val stack_rect :
      'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1
      -> 'a1) -> stack -> 'a1 **)
  
  let rec stack_rect f f0 = function
    | Nil_stack -> f
    | Cons_stack (state_cur, s0, s1) ->
        f0 state_cur s0 s1 (stack_rect f f0 s1)
  
  (** val stack_rec :
      'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1
      -> 'a1) -> stack -> 'a1 **)
  
  let rec stack_rec f f0 = function
    | Nil_stack -> f
    | Cons_stack (state_cur, s0, s1) ->
        f0 state_cur s0 s1 (stack_rec f f0 s1)
  
  (** val state_of_stack : stack -> A.state **)
  
  let state_of_stack = function
    | Nil_stack -> A.Init
    | Cons_stack (s, s0, s1) -> A.Ninit s
  
  (** val pop :
      A.Gram.symbol list -> stack -> A.Gram.symbol list -> tuple ->
      (stack*tuple) result **)
  
  let rec pop symbols_to_pop stack_cur symbols_popped sem_popped =
    match symbols_to_pop with
      | [] -> OK (stack_cur,sem_popped)
      | t::q ->
          (match stack_cur with
             | Nil_stack -> Err
             | Cons_stack (state_cur, sem, stack_rec0) ->
                 if compare_eqdec
                      A.Gram.coq_SymbolAlph.coq_AlphabetComparable
                      (A.last_symb_of_non_init_state state_cur) t
                 then pop q stack_rec0 (t::symbols_popped)
                        (Obj.magic (sem,sem_popped))
                 else Err)
  
  (** val reduce : stack -> A.Gram.production -> stack result **)
  
  let reduce stack_cur production0 =
    bind2
      (pop (rev (A.Gram.prod_rhs production0)) stack_cur [] (Obj.magic ()))
      (fun stack_new sem ->
      match A.goto_table (state_of_stack stack_new)
              (A.Gram.prod_lhs production0) with
        | Some s ->
            let act = A.Gram.prod_action production0 in
            OK (Cons_stack (s,
            (uncurry (List0.map (Obj.magic __) (A.Gram.prod_rhs production0))
              act sem), stack_new))
        | None -> Err)
  
  type step_result =
    | Fail_sr
    | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
    | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  (** val step_result_rect :
      'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
      'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
      'a1 **)
  
  let step_result_rect f f0 f1 = function
    | Fail_sr -> f
    | Accept_sr (x, x0) -> f0 x x0
    | Progress_sr (x, x0) -> f1 x x0
  
  (** val step_result_rec :
      'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
      'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
      'a1 **)
  
  let step_result_rec f f0 f1 = function
    | Fail_sr -> f
    | Accept_sr (x, x0) -> f0 x x0
    | Progress_sr (x, x0) -> f1 x x0
  
  (** val step :
      stack -> A.GramDefs.token coq_Stream -> step_result result **)
  
  let step stack_cur buffer =
    match A.action_table (state_of_stack stack_cur) with
      | Coq_inl accept_action ->
          (match accept_action with
             | A.Default_reduce_act production0 ->
                 bind (reduce stack_cur production0) (fun stack_new -> OK
                   (Progress_sr (stack_new, buffer)))
             | A.Accept_act ->
                 (match stack_cur with
                    | Nil_stack -> Err
                    | Cons_stack (s, sem, s0) ->
                        (match s0 with
                           | Nil_stack ->
                               if compare_eqdec
                                    A.Gram.coq_SymbolAlph.coq_AlphabetComparable
                                    (A.last_symb_of_non_init_state s)
                                    A.Gram.start_symbol
                               then OK (Accept_sr (sem, buffer))
                               else Err
                           | Cons_stack (state_cur, s1, s2) -> Err)))
      | Coq_inr awt ->
          let Coq_existT (term, sem) = hd buffer in
          (match awt term with
             | A.Shift_act state_new -> OK (Progress_sr ((Cons_stack
                 (state_new, sem, stack_cur)), (tl buffer)))
             | A.Reduce_act production0 ->
                 bind (reduce stack_cur production0) (fun stack_new -> OK
                   (Progress_sr (stack_new, buffer)))
             | A.Fail_act -> OK Fail_sr)
  
  type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  (** val parse_result_rect :
      'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1 **)
  
  let parse_result_rect f f0 f1 = function
    | Fail_pr -> f
    | Timeout_pr -> f0
    | Parsed_pr (x, x0) -> f1 x x0
  
  (** val parse_result_rec :
      'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1 **)
  
  let parse_result_rec f f0 f1 = function
    | Fail_pr -> f
    | Timeout_pr -> f0
    | Parsed_pr (x, x0) -> f1 x x0
  
  (** val parse_fix :
      stack -> A.GramDefs.token coq_Stream -> nat -> parse_result result **)
  
  let rec parse_fix stack_cur buffer = function
    | O -> OK Timeout_pr
    | S it ->
        bind (step stack_cur buffer) (fun r ->
          match r with
            | Fail_sr -> OK Fail_pr
            | Accept_sr (t, buffer_new) -> OK (Parsed_pr (t, buffer_new))
            | Progress_sr (s, buffer_new) -> parse_fix s buffer_new it)
  
  (** val parse :
      A.GramDefs.token coq_Stream -> nat -> parse_result result **)
  
  let parse buffer n_steps =
    parse_fix Nil_stack buffer n_steps
 end

module type T = 
 functor (A:T) ->
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
    | Cons_stack of A.noninitstate * A.Gram.symbol_semantic_type * stack
  
  val stack_rect :
    'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1 ->
    'a1) -> stack -> 'a1
  
  val stack_rec :
    'a1 -> (A.noninitstate -> A.Gram.symbol_semantic_type -> stack -> 'a1 ->
    'a1) -> stack -> 'a1
  
  val state_of_stack : stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> A.Gram.symbol list -> tuple ->
    (stack*tuple) result
  
  val reduce : stack -> A.Gram.production -> stack result
  
  type step_result =
    | Fail_sr
    | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
    | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  val step_result_rect :
    'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
    'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
    'a1
  
  val step_result_rec :
    'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream ->
    'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) -> step_result ->
    'a1
  
  val step : stack -> A.GramDefs.token coq_Stream -> step_result result
  
  type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  val parse_result_rect :
    'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream
    -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    'a1 -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token coq_Stream
    -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    stack -> A.GramDefs.token coq_Stream -> nat -> parse_result result
  
  val parse : A.GramDefs.token coq_Stream -> nat -> parse_result result
 end

