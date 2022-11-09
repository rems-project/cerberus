(* this is a placeholder for ocaml_implementation/tags.ml.
   on extraction `tagDefs` should be mapped to `tagDefs` function
   from tags.ml
 *)

Require Import CoqSymbol.
Require Import CoqCtype.

Module Type TagDefs.

  Parameter tagDefs: unit -> (SymMap.t CoqCtype.tag_definition).

End TagDefs.
