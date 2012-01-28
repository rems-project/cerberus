(* Start CoqIDE at ./src/TV *)
Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import alist.
Require Import infrastructure_props.
Require Import CoqListFacts.
Require Import sub_symexe.

Export SBSE.

Definition prefix A (l1 l:list A) := exists l2, l1 ++ l2 = l.

(* A more general way is to check if l1 is a subset of l2. By doing that way,
 * at call-site, we also need to ensure parameters are matched. The prefix
 * checking is sufficient to Softbound.
*)
Lemma prefix_dec : forall A, (forall (a1 a2:A), {a1=a2}+{~a1=a2}) ->
  forall (l1 l2:list A), {prefix _ l1 l2}+{~prefix _ l1 l2}.
Proof.
  induction l1.
    left. exists l2. auto.

    destruct l2.
      right. intro J. destruct J as [l EQ].
      inversion EQ.

      destruct (@H a a0); subst.
        destruct (@IHl1 l2).
          left. destruct p as [l EQ]; subst.
          exists l. auto.

          right. intro J. apply n.
          destruct J as [l EQ].
          inversion EQ; subst.
          exists l. auto.
        right. intro J. destruct J as [l EQ].        
        inversion EQ; subst; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
