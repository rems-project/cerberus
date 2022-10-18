(* this is a placeholder for ocaml_implementation/tags.ml.
   on extraction `tagDefs` should be mapped to `tagDefs` function
   from tags.ml
 *)

Require Import CoqSymbol.
Require Import CoqCtype.

Definition tagDefs: unit -> (SymMap.t CoqCtype.tag_definition) :=
  fun _ => @SymMap.empty _.
