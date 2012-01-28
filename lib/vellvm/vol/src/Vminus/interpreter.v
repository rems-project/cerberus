Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import trace.
Require Import Metatheory.
Require Import alist.
Require Import monad.
Require Import genericvalues.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import syntax.
Require Import infrastructure_props.
Require Import opsem.

Export Opsem.

Definition interInsn (F:fdef) (state:ExecutionContext) 
  : option (ExecutionContext*trace) :=
match state with
| mkEC B cs tmn lc =>
  (* If cs is nil, we check tmn, 
     otherwise, we check the first cmd in cs *)
  match cs with
  | nil => (* terminator *)
    match tmn with
    | insn_return _ _ => None
    | insn_br bid Cond l1 l2 =>
      (* read the value of Cond *)
      do cond0 <- (getOperandValue Cond lc);
      (* look up the target block *)
        match (if isGVZero cond0
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) with
        | None => None
        | Some (block_intro l' ps' cs' tmn') =>
            do lc' <- (switchToNewBasicBlock (block_intro l' ps' cs' 
                      tmn') B lc);
               ret ((mkEC (block_intro l' ps' cs' tmn') cs'
                     tmn' lc'), trace_nil)
        end
    | insn_br_uncond bid l0 =>
      (* look up the target block *)
      match (lookupBlockViaLabelFromFdef F l0) with
      | None => None
      | Some (block_intro l' ps' cs' tmn') =>
          do lc' <- (switchToNewBasicBlock (block_intro l' ps' cs' tmn')
                     B lc);
          ret ((mkEC (block_intro l' ps' cs' tmn') cs' 
                 tmn' lc'), trace_nil)
      end
    end

  | c::cs => (* non-terminator *)
    match c with
    | insn_bop id0 bop0 v1 v2 => 
      do gv3 <- BOP lc bop0 v1 v2;
         ret ((mkEC B cs tmn (updateAddAL _ lc id0 gv3)), trace_nil)
    | insn_icmp id0 cond0 v1 v2 =>
      do gv3 <- ICMP lc cond0 v1 v2;
         ret ((mkEC B cs tmn (updateAddAL _ lc id0 gv3)), trace_nil)
    end
  end
end.

Ltac dos_rewrite :=
  match goal with
  | [ H : _ = true |- _ ] => rewrite H; simpl
  | [ H : _ = ret _ |- _ ] => rewrite H; simpl
  | [ H : ret _ = _ |- _ ] => rewrite <- H; simpl
  | [ H : _ = merror |- _ ] => rewrite H; simpl
  end.

Ltac dos_simpl := simpl; repeat dos_rewrite.

Lemma dsInsn__implies__interInsn : forall F state state' tr,
  sInsn F state state' tr ->
  interInsn F state = Some (state', tr).
Proof. 
  intros F state state' tr HdsInsn.
  (sInsn_cases (destruct HdsInsn) Case); dos_simpl; auto.
Qed.

Lemma interInsn__implies__dsInsn : forall F state state' tr,
  interInsn F state = Some (state', tr) ->
  sInsn F state state' tr.
Proof.
  intros F state state' tr HinterInsn.
  destruct state as [B cs tmn lc]; simpl in HinterInsn;
    try solve [inversion HinterInsn].

    destruct cs.
      destruct tmn; try solve [inversion HinterInsn].
      Case "insn_br".
        remember (getOperandValue v lc) as R1.
        destruct R1; try solve [inversion HinterInsn].
          simpl in HinterInsn.
          remember (isGVZero g) as R3.
          destruct R3.
            remember (lookupBlockViaLabelFromFdef F l1) as R2.
            destruct R2; tinv HinterInsn.
              destruct b.
              remember (switchToNewBasicBlock
                (block_intro l2 p c t) B lc) as R4.
              destruct R4; inv HinterInsn.              
              eapply sBranch; simpl; eauto.
                rewrite <- HeqR3. auto.
        
            remember (lookupBlockViaLabelFromFdef F l0) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              remember (switchToNewBasicBlock
                (block_intro l2 p c t) B lc) as R4.
              destruct R4; inv HinterInsn.
              eapply sBranch; simpl; eauto.    
                rewrite <- HeqR3. auto.

      Case "insn_br_uncond".
        remember (lookupBlockViaLabelFromFdef F l0) as R2.
        destruct R2; inversion HinterInsn; subst.
          destruct b.
          remember (switchToNewBasicBlock 
            (block_intro l1 p c t) B lc) as R3.
          destruct R3; inversion HinterInsn; subst.
          inversion HinterInsn; subst; eauto.

      destruct c.
      Case "insn_bop".
        remember (BOP lc b v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.
          
      Case "insn_icmp".
        remember (ICMP lc c v v0) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


