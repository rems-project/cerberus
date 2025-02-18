Require Import BaseTypes.
Require Import IndexTerms.
Require Import Cerberus.Location.
Require Import Request.
Require Import LogicalConstraints.
Require Import CN.
Require Import Id.
Require Import Sym.
Require Import SCtypes.

(* Show/Have distinction *)
Inductive have_show : Type :=
  | HS_Have : have_show
  | HS_Show : have_show.

(* Extract type *)
Definition extract := (list Id.t * cn_to_extract Symbol.t SCtypes.t * IndexTerms.t)%type.

(* Statement type *)
Inductive statement : Type :=
  | Pack_unpack : pack_unpack -> Request.Predicate.t -> statement
  | To_from_bytes : to_from -> Request.Predicate.t -> statement
  | Have : LogicalConstraints.t -> statement
  | Instantiate : cn_to_instantiate Symbol.t SCtypes.t -> IndexTerms.t -> statement
  | Split_case : LogicalConstraints.t -> statement
  | Extract : extract -> statement
  | Unfold : Sym.t -> list IndexTerms.t -> statement
  | Apply : Sym.t -> list IndexTerms.t -> statement
  | Assert : LogicalConstraints.t -> statement
  | Inline : list Sym.t -> statement
  | Print : IndexTerms.t -> statement.

(* Load record *)
Record load := {
  ct : SCtypes.t;
  pointer : IndexTerms.t
}.

(* Main program type *)
Inductive t : Type :=
  | CLet : Location.t -> (Sym.t * load) -> t -> t
  | Statement : Location.t -> statement -> t. 