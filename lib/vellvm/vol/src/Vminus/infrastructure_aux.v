Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".

Require Import syntax.
Require Import Metatheory.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import monad.
Require Import Decidable.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Memory.
Require Import Kildall.
Require Import Lattice.

Module VMinfra.

Export VMsyntax.

(**********************************)
(* Definition for basic types, which can be refined for extraction. *)

Definition id_dec : forall x y : id, {x=y} + {x<>y} := eq_atom_dec.
Definition l_dec : forall x y : l, {x=y} + {x<>y} := eq_atom_dec.

(**********************************)
(* LabelSet. *)

  Definition lempty_set := empty_set l.
  Definition lset_add (l1:l) (ls2:ls) := set_add eq_dec l1 ls2.
  Definition lset_union (ls1 ls2:ls) := set_union eq_dec ls1 ls2.
  Definition lset_inter (ls1 ls2:ls) := set_inter eq_dec ls1 ls2.
  Definition lset_eqb (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => true
    | _ => false
    end.
  Definition lset_neqb (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => false
    | _ => true
    end.
  Definition lset_eq (ls1 ls2:ls) := lset_eqb ls1 ls2 = true.
  Definition lset_neq (ls1 ls2:ls) := lset_neqb ls1 ls2 = true. 
  Definition lset_single (l0:l) := lset_add l0 (lempty_set). 
  Definition lset_mem (l0:l) (ls0:ls) := set_mem eq_dec l0 ls0.

(**********************************)
(* Inversion. *)

  Definition getCmdLoc (i:cmd) : id :=
  match i with
  | insn_bop id _ v1 v2 => id
  | insn_icmp id cond v1 v2 => id
  end.
 
  Definition getTerminatorID (i:terminator) : id :=
  match i with
  | insn_return id _ => id
  | insn_br id v l1 l2 => id
  | insn_br_uncond id l => id
  end.

  Definition getPhiNodeID (i:phinode) : id :=
  match i with
  | insn_phi id _ => id
  end.

  Definition getValueID (v:value) : option id :=
  match v with
  | value_id id => Some id
  | value_const _ => None
  end.

  Definition getInsnLoc (i:insn) : id :=
  match i with
  | insn_phinode p => getPhiNodeID p
  | insn_cmd c => getCmdLoc c
  | insn_terminator t => getTerminatorID t
  end.

  Definition isPhiNodeB (i:insn) : bool :=
  match i with
  | insn_phinode p => true
  | insn_cmd c => false
  | insn_terminator t => false
  end.  

  Definition isPhiNode (i:insn) : Prop :=
  isPhiNodeB i = true.

  Definition getCmdID (i:cmd) : option id :=
  match i with
  | insn_bop id _ v1 v2 => Some id
  | insn_icmp id cond v1 v2 => Some id
  end.

Fixpoint getCmdsIDs (cs:cmds) : list atom :=
match cs with
| nil => nil
| c::cs' =>
    match getCmdID c with 
    | Some id1 => id1::getCmdsIDs cs'
    | None => getCmdsIDs cs'
    end
end.

Fixpoint getPhiNodesIDs (ps:phinodes) : list atom :=
match ps with
| nil => nil
| p::ps' =>getPhiNodeID p::getPhiNodesIDs ps'
end.

Definition getBlockIDs (b:block) : list atom :=
let '(block_intro _ ps cs _) := b in
getPhiNodesIDs ps ++ getCmdsIDs cs.

  Definition getInsnID (i:insn) : option id :=
  match i with
  | insn_phinode p => Some (getPhiNodeID p)
  | insn_cmd c => getCmdID c
  | insn_terminator t => None
  end.

Lemma getCmdLoc_getCmdID : forall a i0,
  getCmdID a = Some i0 ->
  getCmdLoc a = i0.
Proof.
  intros a i0 H.
  destruct a; inv H; auto.
Qed.

Definition getValueIDs (v:value) : ids :=
match (getValueID v) with
| None => nil
| Some id => id::nil
end.

Fixpoint values2ids (vs:list value) : ids :=
match vs with
| nil => nil
| value_id id::vs' => id::values2ids vs'
| _::vs' => values2ids vs'
end.

Fixpoint list_prj1 (X Y:Type) (ls : list (X*Y)) : list X :=
match ls with
| nil => nil
| (x, y)::ls' => x::list_prj1 X Y ls'
end.

Fixpoint list_prj2 (X Y:Type) (ls : list (X*Y)) : list Y :=
match ls with
| nil => nil
| (x, y)::ls' => y::list_prj2 X Y ls'
end.

Definition getCmdOperands (i:cmd) : ids :=
match i with
| insn_bop _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
| insn_icmp _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
end.

Definition valueInCmdOperands (v0:value) (i:cmd) : Prop :=
match i with
| insn_bop _ _ v1 v2 => v0 = v1 \/ v0 = v2
| insn_icmp _ _ v1 v2 => v0 = v1 \/ v0 = v2
end.

Definition valueInTmnOperands (v0:value) (i:terminator) : Prop :=
match i with
| insn_return _ v => v = v0
| insn_br _ v _ _ => v = v0
| insn_br_uncond _ _ => False
end.

Definition getTerminatorOperands (i:terminator) : ids :=
match i with
| insn_return _ v => getValueIDs v 
| insn_br _ v _ _ => getValueIDs v
| insn_br_uncond _ _ => nil
end.

Definition getPhiNodeOperands (i:phinode) : ids :=
match i with
| insn_phi _ ls => values2ids (list_prj1 _ _ (unmake_list_value_l ls))
end.

Definition getInsnOperands (i:insn) : ids :=
match i with
| insn_phinode p => getPhiNodeOperands p
| insn_cmd c => getCmdOperands c
| insn_terminator t => getTerminatorOperands t
end.

Definition getCmdLabels (i:cmd) : ls :=
match i with
| insn_bop _ _ _ _ => nil
| insn_icmp _ _ _ _ => nil
end.

Definition getTerminatorLabels (i:terminator) : ls :=
match i with
| insn_return _ _ => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond _ l => l::nil
end.

Definition getPhiNodeLabels (i:phinode) : ls :=
match i with
| insn_phi _ ls => list_prj2 _ _ (unmake_list_value_l ls)
end.

Definition getInsnLabels (i:insn) : ls :=
match i with
| insn_phinode p => getPhiNodeLabels p
| insn_cmd c => getCmdLabels c
| insn_terminator tmn => getTerminatorLabels tmn
end.

Definition getCmdsFromBlock (b:block) : cmds :=
match b with
| block_intro l _ li _ => li
(* | block_without_label li => li *)
end.

Definition getPhiNodesFromBlock (b:block) : phinodes :=
match b with
| block_intro l li _ _ => li
(* | block_without_label li => li *)
end.

Definition getTerminatorFromBlock (b:block) : terminator :=
match b with
| block_intro l _ _ t => t
(* | block_without_label li => li *)
end.

Fixpoint getLabelViaIDFromList (ls:list_value_l) (branch:id) : option l :=
match ls with
| Nil_list_value_l => None
| Cons_list_value_l (value_id id) l ls' => 
  match (eq_dec id branch) with
  | left _ => Some l
  | right _ => getLabelViaIDFromList ls' branch
  end
| Cons_list_value_l _ l ls' => getLabelViaIDFromList ls' branch
end.

Definition getLabelViaIDFromPhiNode (phi:phinode) (branch:id) : option l :=
match phi with
| insn_phi _ ls => getLabelViaIDFromList ls branch
end.

Fixpoint getLabelsFromIdls (idls:list_value_l) : ls :=
match idls with
| Nil_list_value_l => lempty_set
| Cons_list_value_l _ l idls' => lset_add l (getLabelsFromIdls idls')
end.

Definition getLabelsFromPhiNode (phi:phinode) : ls :=
match phi with
| insn_phi _ ls => getLabelsFromIdls ls
end.

Fixpoint getLabelsFromPhiNodes (phis:list phinode) : ls :=
match phis with
| nil => lempty_set
| phi::phis' => lset_union (getLabelsFromPhiNode phi) (getLabelsFromPhiNodes phis')
end.

Definition getIDLabelsFromPhiNode p : list_value_l :=
match p with
| insn_phi _ idls => idls
end.

Fixpoint getLabelViaIDFromIDLabels idls id : option l :=
match idls with
| Nil_list_value_l => None
| Cons_list_value_l (value_id id0) l0 idls' => if eq_dec id id0 then Some l0 else getLabelViaIDFromIDLabels idls' id
| Cons_list_value_l _ l0 idls' => getLabelViaIDFromIDLabels idls' id
end.

Definition _getLabelViaIDPhiNode p id : option l :=
match p with
| insn_phi _ ls => getLabelViaIDFromIDLabels ls id
end.

Definition getLabelViaIDPhiNode (phi:insn) id : option l :=
match phi with
| insn_phinode p => _getLabelViaIDPhiNode p id
| _ => None
end.

Fixpoint getValueViaLabelFromValuels (vls:list_value_l) (l0:l) : option value :=
match vls with
| Nil_list_value_l => None
| Cons_list_value_l v l1 vls'=>
  if (eq_dec l1 l0)
  then Some v
  else getValueViaLabelFromValuels vls' l0
end.

Definition getValueViaBlockFromValuels (vls:list_value_l) (b:block) : option value :=
match b with
| block_intro l _ _ _ => getValueViaLabelFromValuels vls l
end.

Definition getValueViaBlockFromPHINode (i:phinode) (b:block) : option value :=
match i with
| insn_phi _ vls => getValueViaBlockFromValuels vls b
end.

Definition getPHINodesFromBlock (b:block) : list phinode :=
match b with
| (block_intro _ lp _ _) => lp
end.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro (b::_) => Some b
| _ => None
end.

Definition getEntryCmds (b:block) : cmds :=
match b with
| block_intro _ _ lc _ => lc
end.

(**********************************)
(* Lookup. *)

(* ID binding lookup *)

Fixpoint lookupCmdViaIDFromCmds (li:cmds) (id0:id) : option cmd :=
match li with
| nil => None
| i::li' =>
   if (eq_atom_dec id0 (getCmdLoc i)) 
   then Some i else lookupCmdViaIDFromCmds li' id0
end.

Fixpoint lookupPhiNodeViaIDFromPhiNodes (li:phinodes) (id0:id) 
  : option phinode :=
match li with
| nil => None
| i::li' =>
    if (eq_dec id0 (getPhiNodeID i)) then Some i 
    else lookupPhiNodeViaIDFromPhiNodes li' id0
end.

Definition lookupInsnViaIDFromBlock (b:block) (id:id) : option insn :=
match b with
| block_intro l ps cs t =>
  match (lookupPhiNodeViaIDFromPhiNodes ps id) with
  | None => 
      match (lookupCmdViaIDFromCmds cs id) with
      | None => None
      | Some c => Some (insn_cmd c)
      end
  | Some re => Some (insn_phinode re)    
  end
end.

Fixpoint lookupInsnViaIDFromBlocks (lb:blocks) (id:id) : option insn :=
match lb with
| nil => None
| b::lb' => 
  match (lookupInsnViaIDFromBlock b id) with
  | None => lookupInsnViaIDFromBlocks lb' id
  | re => re
  end
end.

Definition lookupInsnViaIDFromFdef (f:fdef) (id0:id) : option insn :=
let '(fdef_intro bs) := f in lookupInsnViaIDFromBlocks bs id0.

(* Block lookup from ID *)

Fixpoint lookupBlockViaIDFromBlocks (lb:blocks) (id1:id) : option block :=
match lb with
| nil => None  
| b::lb' => 
  match (In_dec eq_dec id1 (getBlockIDs b)) with
  | left _ => Some b
  | right _ => lookupBlockViaIDFromBlocks lb' id1
  end
end.

Definition lookupBlockViaIDFromFdef (fd:fdef) (id:id) : option block :=
match fd with
| fdef_intro lb => lookupBlockViaIDFromBlocks lb id
end.

(*     ID type lookup                                    *)

Definition lookupIDFromCmd (i:cmd) (id0:id) : option unit := 
  match (getCmdLoc i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some tt
    else None
  end.

Fixpoint lookupIDFromCmds (li:cmds) (id0:id) : option unit :=
match li with
| nil => None
| i::li' => 
  match (lookupIDFromCmd i id0) with
  | None => lookupIDFromCmds li' id0
  | re => re
  end
end.
    
Definition lookupIDFromPhiNode (i:phinode) (id0:id) : option unit :=
  match (getPhiNodeID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some tt
    else None
  end.

Fixpoint lookupIDFromPhiNodes (li:phinodes) (id0:id) : option unit :=
match li with
| nil => None
| i::li' => 
  match (lookupIDFromPhiNode i id0) with
  | None => lookupIDFromPhiNodes li' id0
  | re => re
  end
end.

Definition lookupIDFromTerminator (i:terminator) (id0:id) : option unit :=
  match (getTerminatorID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some tt
    else None
  end.

Definition lookupIDFromBlock (b:block) (id0:id) : option unit :=
match b with
| block_intro l ps cs t =>
  match (lookupIDFromPhiNodes ps id0) with
  | None => 
    match (lookupIDFromCmds cs id0) with
    | None => lookupIDFromTerminator t id0
    | re => re
    end
  | re => re    
  end
end.

Fixpoint lookupIDFromBlocks (lb:blocks) (id0:id) : option unit :=
match lb with
| nil => None
| b::lb' => 
  match (lookupIDFromBlock b id0) with
  | None => lookupIDFromBlocks lb' id0
  | re => re
  end
end.

Definition lookupIDFromFdef (fd:fdef) (id0:id) : option unit :=
match fd with
| (fdef_intro lb) => lookupIDFromBlocks lb id0
end.

(**********************************)
(* labels <-> blocks. *)

  Definition l2block := list (l*block).

  Definition genLabel2Block_block (b:block) : l2block :=
  match b with
  | block_intro l _ _ _ => (l,b)::nil
  end.  

  Fixpoint genLabel2Block_blocks (bs:blocks) : l2block :=
  match bs with 
  | nil => nil
  | b::bs' => (genLabel2Block_block b)++(genLabel2Block_blocks bs')
  end.

  Definition genLabel2Block_fdef (f:fdef) : l2block := 
  match f with
  | fdef_intro blocks => genLabel2Block_blocks blocks
  end.

  Definition getNonEntryOfFdef (f:fdef) : blocks :=
  match f with
  | fdef_intro blocks => 
    match blocks with
    | nil => nil
    | b::blocks' => blocks'
    end 
  end.  

  Definition lookupBlockViaLabelFromBlocks (bs:blocks) (l0:l) : option block :=
  lookupAL _ (genLabel2Block_blocks bs) l0.

  Definition lookupBlockViaLabelFromFdef (f:fdef) (l0:l) : option block :=
  let '(fdef_intro bs) := f in
  lookupAL _ (genLabel2Block_fdef f) l0.
  
  Fixpoint getLabelsFromBlocks (lb:blocks) : ls :=
  match lb with
  | nil => lempty_set
  | (block_intro l0 _ _ _)::lb' => lset_add l0 (getLabelsFromBlocks lb')
  end.

(**********************************)
(* generate block use-def *)

  Definition update_udb (udb:usedef_block) (lu ld:l) : usedef_block :=
  let ls :=
    match lookupAL _ udb ld with
    | Some ls => ls
    | None => nil
    end in
  match (in_dec l_dec lu ls) with
  | left _ => udb
  | right _ => updateAddAL _ udb ld (lu::ls) 
  end.

  Definition genBlockUseDef_block b (udb:usedef_block) : usedef_block :=
  match b with
  | block_intro l0 _ _ tmn2 =>
    match tmn2 with
    | insn_br _ _ l1 l2 => update_udb (update_udb udb l0 l2) l0 l1
    | insn_br_uncond _ l1 => update_udb udb l0 l1
    | _ => udb
    end
  end.

  Fixpoint genBlockUseDef_blocks bs (udb:usedef_block) : usedef_block :=
  match bs with
  | nil => udb
  | b::bs' => genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
  end.

  Definition genBlockUseDef_fdef f2 : usedef_block :=
  match f2 with
  | fdef_intro lb2 => genBlockUseDef_blocks lb2 nil
  end.

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_intro l _ _ _ => l
  end.

  Definition getBlockUseDef (udb:usedef_block) (b:block) : option (list l) :=
  lookupAL _ udb (getBlockLabel b).

(**********************************)
(* CFG. *)

  Definition getTerminator (b:block) : terminator := 
  match b with
  | block_intro l _ _ t => t
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => lempty_set 
  | (_, l0)::cs' => lset_add l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:terminator) : ls := 
  match i with
  | insn_br _ v l1 l2 => lset_add l1 (lset_add l2 lempty_set)
  | insn_br_uncond _ l0 => lset_add l0 lempty_set 
  (* | insn_switch _ t v l0 cls => lset_add l0 (getLabelsFromSwitchCases cls) *)
  (* | insn_invoke id typ id0 ps l1 l2 => lset_add l1 (lset_add l2 lempty_set) *)
  | _ => empty_set l
  end.

  Fixpoint getBlocksFromLabels (ls0:ls) (l2b:l2block): blocks :=
  match ls0 with
  | nil => nil
  | l0::ls0' => 
    match (lookupAL _ l2b l0) with
    | None => getBlocksFromLabels ls0' l2b
    | Some b => b::getBlocksFromLabels ls0' l2b
    end
  end.

  Definition predOfBlock (b:block) (udb:usedef_block) : list l :=
  match (lookupAL _ udb (getBlockLabel b)) with
  | None => nil
  | Some re => re
  end.

  Definition hasSinglePredecessor (b:block) (udb:usedef_block) : bool :=
  match predOfBlock b udb with
  | _::nil => true
  | _ => false
  end.

  Definition hasNonePredecessor (b:block) (udb:usedef_block) : bool :=
  match predOfBlock b udb with
  | nil => true
  | _ => false
  end.

  Definition successors_terminator (tmn: terminator) : ls :=
  match tmn with
  | insn_return _ _ => nil
  | insn_br _ _ l1 l2 => l1::l2::nil
  | insn_br_uncond _ l1 => l1::nil
  end.

(**********************************)
(* Classes. *)

Definition isReturnInsnB (i:terminator) : bool :=
match i with
| insn_return _ _ => true
| _ => false
end.

Definition isBindingCmdB (ib:id_binding) : bool :=
match ib with
| id_binding_cmd _ => true
| _ => false
end.

Definition isBindingTerminatorB (ib:id_binding) : bool :=
match ib with
| id_binding_terminator _ => true
| _ => false
end.

Definition isBindingPhiNodeB (ib:id_binding) : bool :=
match ib with
| id_binding_phinode _ => true
| _ => false
end.

Definition isBindingInsnB (ib:id_binding) : bool :=
isBindingCmdB ib || isBindingTerminatorB ib || isBindingPhiNodeB ib.

Definition isReturnTerminator tmn := isReturnInsnB tmn = true.

Definition isBindingCmd ib : option cmd :=
match ib with
| id_binding_cmd c => Some c
| _ => None
end.

Definition isBindingPhiNode ib : option phinode :=
match ib with
| id_binding_phinode p => Some p
| _ => None
end.

Definition isBindingTerminator ib : option terminator :=
match ib with
| id_binding_terminator tmn => Some tmn
| _ => None
end.

Definition isBindingInsn ib : option insn :=
match ib with
| id_binding_cmd c => Some (insn_cmd c)
| id_binding_phinode p => Some (insn_phinode p)
| id_binding_terminator tmn => Some (insn_terminator tmn)
| _ => None
end.

(*************************************************)
(*         Uniq                                  *)

Fixpoint getCmdsLocs (cs:list cmd) : ids :=
match cs with
| nil => nil
| c::cs' => getCmdLoc c::getCmdsLocs cs'
end.

Definition getBlockLocs b : ids :=
match b with
| block_intro l ps cs t =>
  getPhiNodesIDs ps++getCmdsLocs cs++(getTerminatorID t::nil)
end.

Fixpoint getBlocksLocs bs : ids :=
match bs with
| nil => nil
| b::bs' => getBlockLocs b++getBlocksLocs bs'
end.

Fixpoint getBlocksLabels bs : ls :=
match bs with
| nil => nil
| (block_intro l _ _ _)::bs' => l::getBlocksLabels bs'
end.

Definition uniqBlocks bs : Prop :=
let ls := getBlocksLabels bs in
let ids := getBlocksLocs bs in
NoDup ls /\ NoDup ids.

Definition uniqFdef fdef : Prop :=
match fdef with
| (fdef_intro bs) => uniqBlocks bs
end.

(**********************************)
(* Dec. *)

Definition sumbool2bool A B (dec:sumbool A B) : bool :=
match dec with
| left _ => true
| right _ => false
end.

Lemma sumbool2bool_true : forall A B H,
  sumbool2bool A B H = true -> A.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma sumbool2bool_false : forall A B H,
  sumbool2bool A B H = false -> B.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma eq_sumbool2bool_true : forall A (a1 a2:A) (H:{a1=a2}+{~a1=a2}),
  a1 = a2 ->
  sumbool2bool _ _ H = true.
Proof.
  intros; subst.
  destruct H; auto.
Qed.

Ltac done_right := right; intro J; inversion J; subst; auto.
Lemma bop_dec : forall (b1 b2:bop), {b1=b2}+{~b1=b2}.
Proof.
  decide equality.
Qed.

Lemma cond_dec : forall (c1 c2:cond), {c1=c2}+{~c1=c2}.
Proof.
  decide equality.
Qed.

Lemma const_dec : forall (c1 c2:const), {c1=c2}+{~c1=c2}.
Proof.
  destruct c1; destruct c2.
  destruct (@INTEGER.dec i0 i1); try solve [subst; auto | done_right].
Qed.

Lemma value_dec : forall (v1 v2:value), {v1=v2}+{~v1=v2}.
Proof.
  decide equality.
    destruct (@const_dec c c0); subst; auto.
Qed.    

Lemma list_value_l_dec : forall (l1 l2:list_value_l), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@l_dec l0 l2); subst; try solve [done_right].
    destruct (@IHl1 l3); subst; try solve [auto | done_right].
Qed.

Lemma cmd_dec : forall (c1 c2:cmd), {c1=c2}+{~c1=c2}.
Proof.
  (cmd_cases (destruct c1) Case); destruct c2; try solve [done_right | auto].
  Case "insn_bop".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_icmp".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
Qed.

Lemma terminator_dec : forall (tmn1 tmn2:terminator), {tmn1=tmn2}+{~tmn1=tmn2}.
Proof.
  destruct tmn1; destruct tmn2; try solve [done_right | auto].
  Case "insn_return".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_br".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@l_dec l0 l2); subst; try solve [done_right]. 
    destruct (@l_dec l1 l3); subst; try solve [done_right]. 
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_br_uncond".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@l_dec l0 l1); subst; try solve [auto | done_right]. 
Qed.

Lemma phinode_dec : forall (p1 p2:phinode), {p1=p2}+{~p1=p2}.
Proof.
  destruct p1; destruct p2; try solve [done_right | auto].
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@list_value_l_dec l0 l1); subst; try solve [auto | done_right]. 
Qed.

Lemma insn_dec : forall (i1 i2:insn), {i1=i2}+{~i1=i2}.
Proof.
  destruct i1; destruct i2; try solve [done_right | auto].
    destruct (@phinode_dec p p0); subst; try solve [auto | done_right]. 
    destruct (@cmd_dec c c0); subst; try solve [auto | done_right]. 
    destruct (@terminator_dec t t0); subst; try solve [auto | done_right]. 
Qed.

Lemma cmds_dec : forall (cs1 cs2:list cmd), {cs1=cs2}+{~cs1=cs2}.
Proof.
  induction cs1.
    destruct cs2; subst; try solve [subst; auto | done_right].

    destruct cs2; subst; try solve [done_right].
    destruct (@cmd_dec a c); subst; try solve [done_right].
    destruct (@IHcs1 cs2); subst; try solve [auto | done_right].
Qed.

Lemma phinodes_dec : forall (ps1 ps2:list phinode), {ps1=ps2}+{~ps1=ps2}.
Proof.
  induction ps1.
    destruct ps2; subst; try solve [subst; auto | done_right].

    destruct ps2; subst; try solve [done_right].
    destruct (@phinode_dec a p); subst; try solve [done_right].
    destruct (@IHps1 ps2); subst; try solve [auto | done_right].
Qed.

Lemma block_dec : forall (b1 b2:block), {b1=b2}+{~b1=b2}.
Proof.
  destruct b1; destruct b2; try solve [done_right | auto].
    destruct (@id_dec l0 l1); subst; try solve [done_right]. 
    destruct (@phinodes_dec p p0); subst; try solve [done_right]. 
    destruct (@cmds_dec c c0); subst; try solve [done_right].
    destruct (@terminator_dec t t0); subst; try solve [auto | done_right]. 
Qed.

Lemma blocks_dec : forall (lb lb':blocks), {lb=lb'}+{~lb=lb'}.
Proof.
  induction lb.
    destruct lb'; subst; try solve [subst; auto | done_right].

    destruct lb'; subst; try solve [done_right].
    destruct (@block_dec a b); subst; try solve [done_right].
    destruct (@IHlb lb'); subst; try solve [auto | done_right].
Qed.

Lemma fdef_dec : forall (f1 f2:fdef), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@blocks_dec b b0); subst; try solve [auto | done_right].
Qed.  
(**********************************)
(* Eq. *)
Definition idEqB i i' := sumbool2bool _ _ (id_dec i i').

Definition constEqB c1 c2 := sumbool2bool _ _ (const_dec c1 c2).

Definition valueEqB (v v':value) := sumbool2bool _ _ (value_dec v v').

Definition lEqB i i' := sumbool2bool _ _ (l_dec i i').

Definition list_value_lEqB (idls idls':list_value_l) := sumbool2bool _ _ (list_value_l_dec idls idls').

Definition bopEqB (op op':bop) := sumbool2bool _ _ (bop_dec op op').
Definition condEqB (c c':cond) := sumbool2bool _ _ (cond_dec c c').

Definition cmdEqB (i i':cmd) := sumbool2bool _ _ (cmd_dec i i').

Definition cmdsEqB (cs1 cs2:list cmd) := sumbool2bool _ _ (cmds_dec cs1 cs2).
  
Definition terminatorEqB (i i':terminator) := sumbool2bool _ _ (terminator_dec i i').

Definition phinodeEqB (i i':phinode) := sumbool2bool _ _ (phinode_dec i i').

Definition phinodesEqB (ps1 ps2:list phinode) := sumbool2bool _ _ (phinodes_dec ps1 ps2).

Definition blockEqB (b1 b2:block) := sumbool2bool _ _ (block_dec b1 b2).

Definition blocksEqB (lb lb':blocks) := sumbool2bool _ _ (blocks_dec lb lb').

Definition fdefEqB (fd fd' : fdef) := sumbool2bool _ _ (fdef_dec fd fd').

(**********************************)
(* Inclusion. *)

Fixpoint InCmdsB (i:cmd) (li:cmds) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => cmdEqB i i' || InCmdsB i li'
end.

Fixpoint InPhiNodesB (i:phinode) (li:phinodes) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => phinodeEqB i i' || InPhiNodesB i li'
end.

Definition cmdInBlockB (i:cmd) (b:block) : bool :=
match b with
| block_intro l _ cmds _ => InCmdsB i cmds
end.

Definition phinodeInBlockB (i:phinode) (b:block) : bool :=
match b with
| block_intro l ps _ _ => InPhiNodesB i ps
end.

Definition terminatorInBlockB (i:terminator) (b:block) : bool :=
match b with
| block_intro l _ _ t => terminatorEqB i t
end.

Fixpoint InBlocksB (b:block) (lb:blocks) {struct lb} : bool :=
match lb with
| nil => false
| b' :: lb' => blockEqB b b' || InBlocksB b lb'
end.

Definition blockInFdefB (b:block) (fd:fdef) : bool :=
match fd with
| (fdef_intro lb) => InBlocksB b lb
end.

Definition cmdInFdefBlockB (i:cmd) (f:fdef) (b:block) : bool :=
cmdInBlockB i b && blockInFdefB b f.

Definition phinodeInFdefBlockB (i:phinode) (f:fdef) (b:block) : bool :=
phinodeInBlockB i b && blockInFdefB b f.

Definition terminatorInFdefBlockB (i:terminator) (f:fdef) (b:block) : bool :=
terminatorInBlockB i b && blockInFdefB b f.

Definition insnInBlockB (i : insn) (b : block) :=
match i with
| insn_phinode p => phinodeInBlockB p b
| insn_cmd c => cmdInBlockB c b
| insn_terminator t => terminatorInBlockB t b
end.

Definition insnInFdefBlockB (i:insn) (f:fdef) (b:block) : bool :=
match i with
| insn_phinode p => phinodeInBlockB p b && blockInFdefB b f
| insn_cmd c => cmdInBlockB c b && blockInFdefB b f
| insn_terminator t => terminatorInBlockB t b && blockInFdefB b f
end.

Definition blockInFdef b F := blockInFdefB b F = true.
(**********************************)
(* parent *)

(* matching (cmdInBlockB i b) in getParentOfCmdFromBlocksC directly makes
   the compilation very slow, so we define this dec lemma first... *)
Lemma cmdInBlockB_dec : forall i b,
  {cmdInBlockB i b = true} + {cmdInBlockB i b = false}.
Proof.
  intros i0 b. destruct (cmdInBlockB i0 b); auto.
Qed.

Lemma phinodeInBlockB_dec : forall i b,
  {phinodeInBlockB i b = true} + {phinodeInBlockB i b = false}.
Proof.
  intros i0 b. destruct (phinodeInBlockB i0 b); auto.
Qed.

Lemma terminatorInBlockB_dec : forall i b,
  {terminatorInBlockB i b = true} + {terminatorInBlockB i b = false}.
Proof.
  intros i0 b. destruct (terminatorInBlockB i0 b); auto.
Qed.

Fixpoint getParentOfCmdFromBlocks (i:cmd) (lb:blocks) {struct lb} : option block 
  :=
match lb with
| nil => None
| b::lb' => 
  match (cmdInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfCmdFromBlocks i lb'
  end
end.

Definition getParentOfCmdFromFdef (i:cmd) (fd:fdef) : option block :=
match fd with
| (fdef_intro lb) => getParentOfCmdFromBlocks i lb
end.

Fixpoint getParentOfPhiNodeFromBlocks (i:phinode) (lb:blocks) {struct lb} 
  : option block :=
match lb with
| nil => None
| b::lb' => 
  match (phinodeInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfPhiNodeFromBlocks i lb'
  end
end.

Definition getParentOfPhiNodeFromFdef (i:phinode) (fd:fdef) : option block :=
match fd with
| (fdef_intro lb) => getParentOfPhiNodeFromBlocks i lb
end.

Fixpoint getParentOfTerminatorFromBlocks (i:terminator) (lb:blocks) {struct lb} 
  : option block :=
match lb with
| nil => None
| b::lb' => 
  match (terminatorInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfTerminatorFromBlocks i lb'
  end
end.

Definition getParentOfTerminatorFromFdef (i:terminator) (fd:fdef) : option block 
  :=
match fd with
| (fdef_intro lb) => getParentOfTerminatorFromBlocks i lb
end.

Notation "n =n= n'" := (beq_nat n n') (at level 50).
Notation "b =b= b'" := (blockEqB b b') (at level 50).
Notation "i =cmd= i'" := (cmdEqB i i') (at level 50).
Notation "i =phi= i'" := (phinodeEqB i i') (at level 50).
Notation "i =tmn= i'" := (terminatorEqB i i') (at level 50).

(**********************************)
(* Check to make sure that if there is more than one entry for a
   particular basic block in this PHI node, that the incoming values 
   are all identical. *)
Fixpoint lookupIdsViaLabelFromIdls (idls:list_value_l) (l0:l) : list id :=
match idls with
| Nil_list_value_l => nil
| Cons_list_value_l (value_id id1) l1 idls' =>
  if (eq_dec l0 l1) 
  then set_add eq_dec id1 (lookupIdsViaLabelFromIdls idls' l0)
  else (lookupIdsViaLabelFromIdls idls' l0)
| Cons_list_value_l _ l1 idls' =>
  lookupIdsViaLabelFromIdls idls' l0
end.

Fixpoint _checkIdenticalIncomingValues (idls idls0:list_value_l) : Prop :=
match idls with
| Nil_list_value_l => True
| Cons_list_value_l _ l idls' => 
  (length (lookupIdsViaLabelFromIdls idls0 l) <= 1)%nat /\
  (_checkIdenticalIncomingValues idls' idls0)
end.

Definition checkIdenticalIncomingValues (PN:phinode) : Prop :=
match PN with
| insn_phi _ idls => _checkIdenticalIncomingValues idls idls
end.

(**********************************)
(* Instruction Signature *)

Module Type SigValue.

 Parameter getNumOperands : insn -> nat.

End SigValue.

Module Type SigPHINode.

 Parameter getNumIncomingValues : phinode -> nat.
End SigPHINode.

(* Instruction Instantiation *)

Module Value <: SigValue.

 Definition getNumOperands (i:insn) : nat := 
   length (getInsnOperands i).  

End Value.

Module PHINode <: SigPHINode.

 Definition getNumIncomingValues (i:phinode) : nat :=
 match i with
 | (insn_phi _ ln) => (length (unmake_list_value_l ln))
 end.

End PHINode.

(**********************************)
(* reflect *)

Coercion is_true (b:bool) := b = true.

Inductive reflect (P:Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false
.

End VMinfra.


(*ENDCOPY*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "." "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


