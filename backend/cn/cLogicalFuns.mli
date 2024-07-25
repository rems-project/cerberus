(* Module CLogicalFuns *)

(* TODO: AM: Needs a header explaining what it is *)

(* TODO: BCP: @Apol: Are all of these actually used externally? *)

module SymMap : Map.S with type key = Sym.t

module SymSet : Set.S with type elt = Sym.t

module StringMap : Map.S with type key = String.t

module IntMap : Map.S with type key = Int.t

module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms

val fail_n : TypeErrors.t -> 'a Typing.m

type 'a exec_result =
  | Call_Ret of IT.t
  | Compute of IT.t * 'a
  | If_Else of IT.t * 'a exec_result * 'a exec_result

(* converts mucore values to CN baseterms *)
val mu_val_to_it : IT.loc -> BT.t Mucore.mu_value -> IT.BT.basetype IT.term Option.t

val local_sym_ptr : Cerb_frontend__Symbol.sym

type state =
  { loc_map : IT.t option IntMap.t;
    next_loc : int
  }

type context =
  { label_defs : unit Mucore.mu_label_defs;
    (* map from c functions to logical functions which we are building *)
    c_fun_pred_map : (Locations.t * Sym.t) SymMap.t;
    mu_call_funinfo : (Mucore.symbol, Sctypes.c_concrete_sig) Pmap.map
  }

(* initializes state variable *)
val init_state : state

val mk_local_ptr : state -> IT.loc -> IT.BT.basetype IT.term * state

val is_local_ptr : 'a IT.term -> int Option.m

val get_local_ptr : Locations.t -> 'a IT.term -> int Typing.m

(* updates local state *)
val upd_loc_state : state -> IntMap.key -> IT.t -> state

val triv_simp_ctxt : Simplify.simp_ctxt

val simp_const :
   Locations.t ->
  Cerb_pp_prelude.P.document Lazy.t ->
  IT.t ->
  IndexTerms.BT.basetype IndexTerms.term Typing.m

val do_wrapI :
   IT.loc ->
  Sctypes.ctype ->
  BT.basetype Terms.term ->
  BT.basetype Terms.term Typing.m

(* determines if a term is a numeric constant and permitted to multiply/divide or not*)
val is_const_num : 'a IT.term -> bool

val add_pattern :
   'a Mucore.mu_pattern ->
  'b IT.term ->
  'b IT.term SymMap.t ->
  'b IT.term SymMap.t Typing.m

val signed_int_ity : Sctypes.IntegerTypes.integerType

val signed_int_ty : Memory.BT.basetype

val is_two_pow :
   'a IT.term ->
  ([> `Two_loc of IT.loc ] * [> `Exp of 'a Terms.term ]) option

val bool_rep_ty : Memory.BT.basetype

val bool_ite_1_0 :
   IT.BT.basetype ->
  IT.BT.basetype IT.term ->
  IT.loc ->
  IT.BT.basetype IT.term

(* evalutes a function, handles type different application results *)
val eval_mu_fun :
   Mucore.mu_function ->
  Mucore.IT.BT.basetype Terms.term list ->
  WellTyped.TE.BT.t Mucore.mu_pexpr ->
  Mucore.IT.BT.basetype Mucore.IT.term Typing.m

(* pure expressions have symbolic execution performed on them *)
val symb_exec_mu_pexpr :
   context ->
  IT.BT.basetype IT.term SymMap.t ->
  BT.t Mucore.mu_pexpr ->
  IT.BT.basetype IT.term Typing.m

(* impure expressions have symbolic execution performed on them *)
val symb_exec_mu_expr :
   context ->
  state * IT.BT.basetype IT.term SymMap.t ->
  BT.t Mucore.mu_expr ->
  state exec_result Typing.m

(* determines if pattern is a wild card *)
val is_wild_pat : 'a Mucore.mu_pattern -> bool

(* filters pattern matching so it is filled with valid symbols*)
val filter_syms : Mucore.SymSet.t -> 'a Mucore.mu_pattern -> 'a Mucore.mu_pattern

(* get return value if it is valid to do so*)
val get_ret_it :
   Locations.t ->
  'a Mucore.mu_expr ->
  BT.basetype ->
  'b exec_result ->
  IT.t Typing.m

val c_fun_to_it :
   Locations.t ->
  context ->
  Sym.t ->
  Cerb_frontend.Symbol.sym ->
  LogicalFunctions.definition ->
  unit Mucore.mu_fun_map_decl ->
  BT.basetype IndexTerms.term Typing.m

(* updates logical function if it doesn't exist already else it issues a message *)
val upd_def : Locations.t * Sym.t * LogicalFunctions.IT.t -> unit Typing.m

(* converts C functions to logical functions *)
val add_logical_funs_from_c :
   (Mucore.symbol, Sctypes.c_concrete_sig) Pmap.map ->
  Mucore.mu_function_to_convert list ->
  (Sym.t, unit Mucore.mu_fun_map_decl) Pmap.map ->
  unit Typing.m
