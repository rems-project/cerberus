(* this is a placeholder for ocaml_implementation/tags.ml.
   on extraction `tagDefs` should be mapped to `tagDefs` function
   from tags.ml
 *)

Require Import Symbol.
Require Import Ctype.

Definition tagDefs: unit -> (SymMap.t Ctype.tag_definition) :=
  fun _ => @SymMap.empty _.
