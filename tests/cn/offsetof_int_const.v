From MuCore Require Import Annot ArgumentTypes Core BaseTypes CN CNProgs Ctype False Id ImplMem IndexTerms IntegerType Location Locations LogicalArgumentTypes LogicalConstraints LogicalReturnTypes Memory MuCore Request ReturnTypes SCtypes Sym Symbol Terms Undefined Utils.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import ZArith.


(* Global definitions *)
(* Function definitions *)
Definition __builtin_ctzl  := (ProcDecl unit Loc_unknown None).

Definition __builtin_ctzll  := (ProcDecl unit Loc_unknown None).


