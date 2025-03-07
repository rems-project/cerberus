Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Locations.
Require Import BaseTypes.
Require Import IndexTerms.
Require Import Sym.
Require Import LogicalConstraints.
Require Import Resource.
Require Import Global.

Definition l_info := (Locations.t * string)%type.

Inductive basetype_or_value : Type :=
  | BaseType : BaseTypes.t -> basetype_or_value
  | Value : IndexTerms.t -> basetype_or_value.

Record t := mk_context {
  computational : SymMap.t (basetype_or_value * l_info);
  logical : SymMap.t (basetype_or_value * l_info);
  resources : ((list (Resource.t * Z)) * Z)%type;
  constraints : LogicalConstraints.LCSet.t;
  global : Global.t
}.

(* Helper function *)
Definition get_rs (ctxt : t) := List.map fst (fst ctxt.(resources)).
