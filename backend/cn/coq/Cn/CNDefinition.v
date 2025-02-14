(* This file corresponds to `definition.mli` in the OCaml. Rename to avoid name clashes with Coq keyword *)

Require Import Locations.
Require Import IndexTerms.
Require Import LogicalArgumentTypes.
Require Import Sym.
Require Import BaseTypes.

Module Function.
  Inductive function_body : Type :=
  | Def : IndexTerms.t -> function_body
  | Rec_Def : IndexTerms.t -> function_body
  | Uninterp : function_body.

  (* All field name prefix with `def_function_` to avoid name clashes *)
  Record t := mk_t {
    def_function_loc : Locations.t;
    def_function_args : list (Symbol.t * BaseTypes.t);
    def_function_return_bt : BaseTypes.t;
    def_function_emit_coq : bool;
    def_function_body : function_body
  }.
End Function.

Record Clause_t := mkClause {
  clause_loc : Locations.t;
  clause_guard : IndexTerms.t;
  clause_packing_ft : LogicalArgumentTypes.packing_ft
}.

(* All field name prefix with `def_predicate_` to avoid name clashes *)
Record Predicate_t := mkPredicate {
  def_predicate_loc : Locations.t;
  def_predicate_pointer : Sym.t;
  def_predicate_iargs : list (Sym.t * BaseTypes.t);
  def_predicate_oarg_bt : BaseTypes.t;
  def_predicate_clauses : option (list Clause_t)
}.
