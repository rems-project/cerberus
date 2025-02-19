Require Import Sym.
Require Import SCtypes.
Require Import Memory.
Require Import BaseTypes.
Require Import CNDefinition.
Require Import Locations.
Require Import ArgumentTypes.

Record t := mk_t {
  struct_decls : Memory.struct_decls;
  datatypes : SymMap.t BaseTypes.dt_info;
  datatype_constrs : SymMap.t BaseTypes.constr_info;
  datatype_order : option (list (list Sym.t));
  fun_decls : SymMap.t (Locations.t * option ArgumentTypes.ft * SCtypes.c_concrete_sig);
  resource_predicates : SymMap.t CNDefinition.Predicate_t;
  resource_predicate_order : option (list (list Sym.t));
  logical_functions : SymMap.t CNDefinition.Function.t;
  logical_function_order : option (list (list Sym.t));
  (* lemmata : SymMap.t (Locations.t * ArgumentTypes.lemmat) TODO *)
}.
