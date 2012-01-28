Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import syntax.
Require Import infrastructure.
Require Import typings.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import targetdata.
Require Import opsem.
Require Import dopsem.
Require Import sb_def.
Require Import sb_ds_trans.
Require Import sb_metadata.
Require Import sb_msim.
Require Import sb_ds_gv_inject.

Ltac zauto := auto with zarith.
Ltac zeauto := eauto with zarith.

Import LLVMsyntax.
Import LLVMgv.
Import LLVMtd.
Import LLVMinfra.
Import LLVMtypings.
Import SB_ds_pass.

(* Simulation *)

Definition DGVMap := @Opsem.GVsMap DGVs.

Definition reg_simulation (mi:MoreMem.meminj) TD gl (F:fdef) 
  (rm1:SBspecAux.rmetadata) (rm2:rmap) (lc1 lc2:DGVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall vp blk1 bofs1 eofs1, 
  SBspecAux.get_reg_metadata TD gl rm1 vp = 
    Some (SBspecAux.mkMD blk1 bofs1 eofs1) -> 
  exists bv2, exists ev2, exists bgv2, exists egv2,
    get_reg_metadata rm2 vp = Some (bv2, ev2) /\
    getOperandValue TD bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD ev2 lc2 gl = Some egv2 /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2
) /\
(forall i0 gv1, lookupAL _ lc1 i0 = Some gv1 -> In i0 (getFdefLocs F)).

Definition mem_simulation (mi:MoreMem.meminj) TD (mgb:Values.block) 
  (MM1:SBspecAux.mmetadata) (Mem1 Mem2:mem) : Prop :=
MoreMem.mem_inj mi Mem1 Mem2 /\
0 <= mgb < Mem.nextblock Mem2 /\
(forall b1 ofs1, b1 >= Mem.nextblock Mem1 -> MM1 b1 ofs1 = None) /\
(forall lc2 gl b ofs blk bofs eofs als bid0 eid0 pgv' fs F B cs tmn S Ps 
    EC v cm,  
  wf_globals mgb gl -> 
  SBspecAux.get_mem_metadata TD MM1 ((Vptr b ofs,cm)::nil) = 
    SBspecAux.mkMD blk bofs eofs -> 
  gv_inject mi ((Vptr b ofs,cm)::nil) pgv' ->
  @Opsem.getOperandValue DGVs TD v lc2 gl = Some pgv' ->
  exists bgv', exists egv',
  Opsem.sop_star (OpsemAux.mkCfg S TD Ps gl fs)
    (Opsem.mkState 
      ((Opsem.mkEC F B 
        (insn_call bid0 false attrs gmb_typ gmb_fn 
                       ((p8,nil,v)::
                        (p8,nil,vnullp8)::
                        (i32,nil,vint1)::
                        (p32,nil,vnullp32)::
                        nil)::
         insn_call eid0 false attrs gme_typ gme_fn 
                       ((p8,nil,v)::
                        (p8,nil,vnullp8)::
                        (i32,nil,vint1)::
                        (p32,nil,vnullp32)::
                        nil)::
         cs) 
        tmn lc2 als)
        ::EC) Mem2)
    (Opsem.mkState
       ((Opsem.mkEC F B cs tmn 
         (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als)::EC) 
         Mem2)
    trace_nil /\
    gv_inject mi ((Vptr blk bofs, AST.Mint 31)::nil) bgv' /\
    gv_inject mi ((Vptr blk eofs, AST.Mint 31)::nil) egv'
).

Fixpoint als_simulation (mi:MoreMem.meminj) (als1 als2:list mblock) : Prop :=
  match (als1, als2) with
  | (nil, nil) => True
  | (b1::als1', b2::als2') => 
      mi b1 = Some (b2, 0) /\ als_simulation mi als1' als2'
  | _ => False
  end.

Definition label_of_block (b:block) : l :=
match b with
| block_intro l1 _ _ _ => l1
end.

Definition is_user_function fh1 :=
match fh1 with
| (fheader_intro _ _ fid _ _) => isCallLib fid = false
end.

Definition sbEC_simulates_EC_tail (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbEC:SBspec.ExecutionContext) (EC:Opsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBspec.mkEC f1 b1 ((insn_call i0 nr ca t0 v p)::cs13) tmn1 lc1 rm1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       is_user_function fh1 /\ 
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\ als_simulation mi als1 als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++(insn_call i0 nr ca t0 v p)::cs13) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23, exists cs24,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 /\
         incl ex_ids ex_ids3 /\ 
         call_suffix i0 nr ca t0 v p rm2 = Some cs22 /\
         (*wf_freshs ex_ids3 cs13 rm2 /\*)
         trans_cmds ex_ids3 rm2 cs13 = Some (ex_ids4,cs23) /\
         trans_terminator rm2 tmn1 = Some cs24 /\
         cs2 = cs22 ++ cs23 ++ cs24
  | _ => False
  end.

Definition sbEC_simulates_EC_head (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbEC:SBspec.ExecutionContext) (EC:Opsem.ExecutionContext) : Prop :=
  match (sbEC, EC) with
  | (SBspec.mkEC f1 b1 cs12 tmn1 lc1 rm1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       let '(fdef_intro fh1 bs1) := f1 in
       let '(fdef_intro fh2 bs2) := f2 in
       let '(los, nts) := TD in
       is_user_function fh1 /\ 
       blockInFdefB b1 f1 = true /\
       InProductsB (product_fdef f1) Ps1 = true /\
       trans_fdef nts f1 = Some f2 /\
       tmn1 = tmn2 /\ als_simulation mi als1 als2 /\
       (label_of_block b1 = label_of_block b2) /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs12) tmn1) /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       exists ex_ids, exists rm2, 
       exists ex_ids3, exists ex_ids4, exists cs22, exists cs23,
         gen_metadata_fdef nts (getFdefLocs f1) nil f1 = Some (ex_ids, rm2) /\
         reg_simulation mi TD gl f1 rm1 rm2 lc1 lc2 /\
         incl ex_ids ex_ids3 /\ 
         (*wf_freshs ex_ids3 cs12 rm2 /\*)
         trans_cmds ex_ids3 rm2 cs12 = Some (ex_ids4,cs22) /\
         trans_terminator rm2 tmn1 = Some cs23 /\
         cs2 = cs22 ++ cs23
  end.

Fixpoint sbECs_simulate_ECs_tail (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbECs:SBspec.ECStack) (ECs:Opsem.ECStack) : Prop :=
  match sbECs, ECs with
  | nil, nil => True
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_tail TD Ps1 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD Ps1 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition sbECs_simulate_ECs (TD:TargetData) Ps1 gl (mi:MoreMem.meminj) 
  (sbECs:SBspec.ECStack) (ECs:Opsem.ECStack) : Prop :=
  match sbECs, ECs with
  | sbEC::sbECs', EC::ECs' => 
      sbEC_simulates_EC_head TD Ps1 gl mi sbEC EC /\ 
      sbECs_simulate_ECs_tail TD Ps1 gl mi sbECs' ECs'
  | _, _ => False
  end.

Definition ftable_simulation mi fs1 fs2 : Prop :=
  forall fv1 fv2, gv_inject mi fv1 fv2 ->
    OpsemAux.lookupFdefViaGVFromFunTable fs1 fv1 = 
    OpsemAux.lookupFdefViaGVFromFunTable fs2 fv2.

Definition sbState_simulates_State (mi:MoreMem.meminj) (mgb:Values.block)
  (sbCfg:OpsemAux.Config) (sbSt:SBspec.State) 
  (Cfg:OpsemAux.Config) (St:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := sbCfg in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg in
  match (sbSt, St) with
  | (SBspec.mkState ECs1 M1 MM1,
     Opsem.mkState ECs2 M2) =>
      let '(los, nts) := TD1 in
      wf_system nil S1 /\
      moduleInSystemB (module_intro los nts Ps1) S1 = true /\
      trans_system S1 = Some S2 /\ 
      TD1 = TD2 /\ 
      trans_products nts Ps1 = Some Ps2 /\ 
      sbECs_simulate_ECs TD1 Ps1 gl1 mi ECs1 ECs2 /\
      gl1 = gl2 /\ 
      ftable_simulation mi fs1 fs2 /\ 
      wf_globals mgb gl1 /\
      wf_sb_mi mgb mi M1 M2 /\
      mem_simulation mi TD1 mgb MM1 M1 M2
  end.

Fixpoint params_simulation TD gl mi (lc2 : DGVMap) 
  (ogvs:list (GenericValue * option metadata)) n (cs:cmds) : Prop :=
match (ogvs, cs) with
| (nil, nil) => True
| ((gv, Some (mkMD blk bofs eofs))::ogvs, c1::c2::cs') =>
    exists bv2, exists ev2, exists bgv2, exists egv2, 
      c1 = insn_call fake_id true attrs ssb_typ ssb_fn 
                 ((p8,nil,bv2)::(val32 n)::nil) /\
      c2 = insn_call fake_id true attrs sse_typ sse_fn 
                 ((p8,nil,ev2)::(val32 n)::nil) /\
      getOperandValue TD bv2 lc2 gl = Some bgv2 /\
      getOperandValue TD ev2 lc2 gl = Some egv2 /\
      gv_inject mi ((Vptr blk bofs, AST.Mint 31)::nil) bgv2 /\
      gv_inject mi ((Vptr blk eofs, AST.Mint 31)::nil) egv2 /\
      params_simulation TD gl mi lc2 ogvs (n+1) cs'
| ((gv, None)::ogvs, c1::c2::cs') =>
    params_simulation TD gl mi lc2 ogvs (n+1) cs'
| _ => False
end.

Fixpoint incomingValues_simulation (mi:Values.meminj)
  (re1:list (id * GenericValue * monad metadata))(rm2:rmap)
  (re2:list (id * GenericValue)) : Prop :=
match (re1, re2) with
| (nil, nil) => True
| ((i1,gv1,None)::re1', (i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ incomingValues_simulation mi re1' rm2 re2'
| ((i1,gv1,Some (SBspecAux.mkMD blk1 bofs1 eofs1))::re1', 
   (eid2,egv2)::(bid2,bgv2)::(i2,gv2)::re2') =>
    i1 = i2 /\ gv_inject mi gv1 gv2 /\ 
    lookupAL _ rm2 i2 = Some (bid2,eid2) /\
    gv_inject mi ((Vptr blk1 bofs1, AST.Mint 31)::nil) bgv2 /\  
    gv_inject mi ((Vptr blk1 eofs1, AST.Mint 31)::nil) egv2 /\
    incomingValues_simulation mi re1' rm2 re2'
| _ => False
end.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)
