Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../TV".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import extraction_core.
Require Import eq_tv_dec.
Require Import eq_tv.
Require Import sub_tv_def.
Require Import sub_tv_infer.
Require Import sub_tv_dec.
Require Import sub_tv.
Require Import symexe_def.
Require Import sub_symexe.

(* TV *)
Extract Inductive onat => int [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant SBSE.isCallLib => "Symexe_aux.isCallLib".
Extract Constant SBSE.callLib => "Symexe_aux.callLib".
Extract Constant rename_id => "Symexe_aux.rename_id".
Extract Constant rename_fid => "Symexe_aux.rename_fid".
Extract Constant rename_fid_inv => "Symexe_aux.rename_fid_inv".
Extract Constant smem_lib_sub => "Symexe_aux.smem_lib_sub".
Extract Constant is_hashLoadBaseBound => "Symexe_aux.is_hashLoadBaseBound".
Extract Constant is_hashStoreBaseBound => "Symexe_aux.is_hashStoreBaseBound".
Extract Constant is_loadStoreDereferenceCheck => 
  "Symexe_aux.is_loadStoreDereferenceCheck".
Extract Constant is_callDereferenceCheck => "Symexe_aux.is_callDereferenceCheck".
Extract Constant get_metadata => "Symexe_aux.get_metadata".
Extract Constant get_addrof_be => "Symexe_aux.get_addrof_be".
Extract Constant l_of_arg => "Symexe_aux.l_of_arg".
Extract Constant syscall_returns_pointer => "Symexe_aux.syscall_returns_pointer".
Extract Constant is_tmp_var => "Symexe_aux.is_tmp_var".
Extract Constant eq_INT_Z => "Symexe_aux.eq_INT_Z".

Extraction Library symexe_def.
Extraction Library eq_tv_dec.
Extraction Library eq_tv.
Extraction Library sub_symexe.
Extraction Library sub_tv_def.
Extraction Library sub_tv_dec.
Extraction Library sub_tv_infer.
Extraction Library sub_tv.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
