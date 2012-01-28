Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../Transforms".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import extraction_core.
Require Import dtree.
Require Import primitives.
Require Import gvn.
Require Import mem2reg.

Extract Constant print_reachablity => "Transforms_aux.print_reachablity".
Extract Constant print_dominators => "Transforms_aux.print_dominators".
Extract Constant print_dtree => "Transforms_aux.print_dtree".
Extract Constant TNAME => "int".
Extract Constant init_expected_name => "Transforms_aux.init_expected_name".
Extract Constant check_bname => "Transforms_aux.check_bname".
Extract Constant check_vname => "Transforms_aux.check_vname".
Extract Constant does_pre => "Transforms_aux.does_pre".
Extract Constant does_load_elim => "Transforms_aux.does_load_elim".
Extract Constant does_phi_elim => "Transforms_aux.does_phi_elim".
Extract Constant does_macro_m2r => "Transforms_aux.does_macro_m2r".
Extract Constant does_stld_elim => "Transforms_aux.does_stld_elim".

Extract Constant open_aa_db => "Transforms_aux.open_aa_db".
Extract Constant read_aa_from_fun => "Transforms_aux.read_aa_from_fun".
Extract Constant is_no_alias_id => "Transforms_aux.is_no_alias".
Extract Constant is_must_alias_id => "Transforms_aux.is_must_alias".

Extraction Library dtree.
Extraction Library primitives.
Extraction Library gvn.
Extraction Library mem2reg.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/Transforms") ***
*** End: ***
 *)
