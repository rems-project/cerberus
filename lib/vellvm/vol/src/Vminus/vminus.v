Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Export alist.
Require Export Integers.
Require Export Coqlib.
Require Export monad.
Require Export trace.
Require Export Metatheory.
Require Export Znumtheory.
Require Import syntax.
Require Import infrastructure.
Require Export analysis.
Require Import typings.
Require Import genericvalues.
Require Export infrastructure_props.
Require Export typings_props.
Require Export opsem.
Require Export opsem_props.
Require Export opsem_wf.

Export VMsyntax.
Export VMinfra.
Export VMgv.
Export VMtypings.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
