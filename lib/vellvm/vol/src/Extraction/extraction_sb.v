Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../SoftBound".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import extraction_core.
Require Import sb_def.
Require Import sb_ds_trans.

Extract Constant SBspecAux.bound2MD => "Softbound_aux.bound2MD".
Extract Constant SBspecAux.get_reg_metadata => "Softbound_aux.get_reg_metadata".

Extract Constant SB_ds_pass.assert_fid => "Softbound_aux.assert_mptr_fid".
Extract Constant SB_ds_pass.fake_id => "Softbound_aux.fake_id".
(*Extract Constant SB_ds_pass.gmd_fid => 
  "Softbound_aux.get_mmetadata_fid".*)
Extract Constant SB_ds_pass.gmb_fid => 
  "Softbound_aux.get_mmetadata_base_fid".
Extract Constant SB_ds_pass.gme_fid => 
  "Softbound_aux.get_mmetadata_bound_fid".
Extract Constant SB_ds_pass.smmd_fid => 
  "Softbound_aux.set_mmetadata_fid".
Extract Constant SB_ds_pass.ssb_fid => 
  "Softbound_aux.set_shadowstack_base_fid".
Extract Constant SB_ds_pass.sse_fid =>
  "Softbound_aux.set_shadowstack_bound_fid".
Extract Constant SB_ds_pass.gsb_fid =>
  "Softbound_aux.get_shadowstack_base_fid".
Extract Constant SB_ds_pass.gse_fid =>
  "Softbound_aux.get_shadowstack_bound_fid".
Extract Constant SB_ds_pass.astk_fid =>
  "Softbound_aux.allocate_shadowstack_fid".
Extract Constant SB_ds_pass.dstk_fid =>
  "Softbound_aux.free_shadowstack_fid".
Extract Constant SB_ds_pass.wrapper_fid => "Softbound_aux.wrapper_fid".
Extract Constant SB_ds_pass.isSysLib => "Symexe_aux.isSysLib".
Extract Constant SB_ds_pass.isCallLib => "Symexe_aux.isCallLib".

Extraction Library sb_def.
Extraction Library sb_ds_trans.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/SoftBound") ***
*** End: ***
 *)
