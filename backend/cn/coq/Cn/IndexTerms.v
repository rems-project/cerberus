Require Import List.

Require Import BaseTypes.
Require Import Terms.

(* Type aliases *)
Definition t' := term BaseTypes.t.
Definition t := annot BaseTypes.t.

(* Pattern-related types *)
Definition bindings (bt: Type) := list (pattern bt * option (annot bt)).
Definition t_bindings := bindings BaseTypes.t. 