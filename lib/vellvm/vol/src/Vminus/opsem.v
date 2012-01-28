Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import infrastructure_props.
Require Import typings.
Require Import typings_props.

(************** Opsem ***************************************************** ***)

Module Opsem. 

Export VMsyntax.
Export VMinfra.
Export VMgv.
Export VMtypings.

(**************************************)
(** Execution contexts *)

Record ExecutionContext : Type := mkEC {
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVMap                 (* LLVM values used in this invocation *)
}.

Fixpoint getIncomingValuesForBlockFromPHINodes (PNs:list phinode) (b:block) 
  (locals:GVMap) : option GVMap :=
match PNs with
| nil => Some nil
| (insn_phi id0 vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue v locals, 
             getIncomingValuesForBlockFromPHINodes PNs b locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end               
  end
end.

Fixpoint updateValuesForNewBlock (ResultValues:GVMap) (locals:GVMap) : GVMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' => 
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

Definition switchToNewBasicBlock (Dest:block) (PrevBB:block) (locals:GVMap)
  : option GVMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes PNs PrevBB locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

(***************************************************************)
(* deterministic small-step *)

Inductive sInsn : fdef -> ExecutionContext -> ExecutionContext -> trace -> Prop :=
| sBranch : forall F B lc bid Cond l1 l2 c l' ps' cs' tmn' lc',   
  getOperandValue Cond lc = Some c ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock (block_intro l' ps' cs' tmn') B lc = Some lc'->
  sInsn F
    (mkEC B nil (insn_br bid Cond l1 l2) lc)
    (mkEC (block_intro l' ps' cs' tmn') cs' tmn' lc')
    trace_nil

| sBranch_uncond : forall F B lc bid l l' ps' cs' tmn' lc',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock (block_intro l' ps' cs' tmn') B lc = Some lc'->
  sInsn F
    (mkEC B nil (insn_br_uncond bid l) lc)
    (mkEC (block_intro l' ps' cs' tmn') cs' tmn' lc')
    trace_nil 

| sBop: forall F B lc id bop v1 v2 gvs3 cs tmn,
  BOP lc bop v1 v2 = Some gvs3 ->
  sInsn F
    (mkEC B ((insn_bop id bop v1 v2)::cs) tmn lc) 
    (mkEC B cs tmn (updateAddAL _ lc id gvs3))
    trace_nil 

| sIcmp : forall F B lc id cond v1 v2 gvs3 cs tmn,
  ICMP lc cond v1 v2 = Some gvs3 ->
  sInsn F  
    (mkEC B ((insn_icmp id cond v1 v2)::cs) tmn lc) 
    (mkEC B cs tmn (updateAddAL _ lc id gvs3))
    trace_nil
.

Definition s_genInitState (F:fdef) : option ExecutionContext :=
  match (getEntryBlock F) with
  | None => None
  | Some (block_intro l ps cs tmn) => 
          Some
            (mkEC
              (block_intro l ps cs tmn) 
              cs
              tmn
              nil
            )
   end.

Definition s_isFinialState (state:ExecutionContext) : bool :=
match state with
| mkEC _ nil (insn_return _ _) _ => true
| _ => false
end.

Inductive sop_star (F:fdef) : 
  ExecutionContext -> ExecutionContext -> trace -> Prop :=
| sop_star_nil : forall state, sop_star F state state trace_nil
| sop_star_cons : forall state1 state2 state3 tr1 tr2,
    sInsn F state1 state2 tr1 ->
    sop_star F state2 state3 tr2 ->
    sop_star F state1 state3 (trace_app tr1 tr2)
.

Inductive sop_plus (F:fdef) : ExecutionContext -> ExecutionContext -> trace -> Prop :=
| sop_plus_cons : forall state1 state2 state3 tr1 tr2,
    sInsn F state1 state2 tr1 ->
    sop_star F state2 state3 tr2 ->
    sop_plus F state1 state3 (trace_app tr1 tr2)
.

CoInductive sop_diverges (F:fdef) : ExecutionContext -> Trace -> Prop :=
| sop_diverges_intro : forall state1 state2 tr1 tr2,
    sop_plus F state1 state2 tr1 ->
    sop_diverges F state2 tr2 ->
    sop_diverges F state1 (Trace_app tr1 tr2)
.

Inductive s_converges : fdef -> ExecutionContext -> Prop :=
| s_converges_intro : forall F IS FS tr,
  s_genInitState F = Some IS ->
  sop_star F IS FS tr ->
  s_isFinialState FS ->
  s_converges F FS
.

Inductive s_diverges : fdef -> Trace -> Prop :=
| s_diverges_intro : forall F IS tr,
  s_genInitState F = Some IS ->
  sop_diverges F IS tr ->
  s_diverges F tr
.

Inductive s_goeswrong : fdef -> ExecutionContext -> Prop :=
| s_goeswrong_intro : forall F IS FS tr,
  s_genInitState F = Some IS ->
  sop_star F IS FS tr ->
  ~ s_isFinialState FS ->
  s_goeswrong F FS
.

Hint Constructors sInsn sop_star sop_diverges sop_plus.

End Opsem.

Tactic Notation "sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sBranch" | c "sBranch_uncond" | c "sBop" | c "sIcmp" ].

Tactic Notation "sop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "sop_star_nil" | c "sop_star_cons" ].

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
