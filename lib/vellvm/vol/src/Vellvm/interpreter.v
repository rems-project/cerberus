Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
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
Require Import dopsem.

Export Opsem.

Definition interInsn (cfg:Config) (state:@State DGVs) : option (State*trace) :=
let '(mkCfg Sys TD Ps gl fs) := cfg in
(* Check if the stack is empty. *) 
match state with
| mkState nil Mem0 => None
| mkState ((mkEC F B cs tmn lc als)::EC) Mem0 =>
  (* If cs is nil, we check tmn, 
     otherwise, we check the first cmd in cs *)
  match cs with
  | nil => (* terminator *)
    match tmn with
    | insn_return rid RetTy Result =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c') 
        then 
          do Mem' <- free_allocas TD Mem0 als;
          do lc'' <- returnUpdateLocals TD c' Result lc lc' gl;
             ret ((mkState ((mkEC F' B' cs' tmn' lc'' als')::EC'') Mem'), 
                  trace_nil)
        else None
      end
    | insn_return_void rid =>
      (* the suspended stacks cannot be empty, and
          there must be a caller of the current function. *)
      match EC with
      | nil => None
      | (mkEC F' B' nil tmn' lc' als')::EC'' => None
      | (mkEC F' B' (c'::cs') tmn' lc' als')::EC'' =>
        (* there must be a caller of the current function. *)
        if (Instruction.isCallInst c')
        then
          match (getCallerReturnID c') with 
          | None =>
              do Mem' <- free_allocas TD Mem0 als;
                 ret ((mkState ((mkEC F' B' cs' tmn' lc' als')::EC'') Mem'), 
                      trace_nil)
          | _ => None
          end
        else None
      end
    | insn_br bid Cond l1 l2 =>
      (* read the value of Cond *)
      do cond0 <- (getOperandValue TD Cond lc gl);
      (* look up the target block *)
        match (if isGVZero TD cond0
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) with
        | None => None
        | Some (block_intro l' ps' cs' tmn') =>
            do lc' <- (switchToNewBasicBlock TD (block_intro l' ps' cs' 
                      tmn') B gl lc);
               ret ((mkState ((mkEC F (block_intro l' ps' cs' tmn') cs'
                     tmn' lc' als)::EC) Mem0), trace_nil)
        end
    | insn_br_uncond bid l0 =>
      (* look up the target block *)
      match (lookupBlockViaLabelFromFdef F l0) with
      | None => None
      | Some (block_intro l' ps' cs' tmn') =>
          do lc' <- (switchToNewBasicBlock TD (block_intro l' ps' cs' tmn')
                     B gl lc);
          ret ((mkState ((mkEC F (block_intro l' ps' cs' tmn') cs' 
                 tmn' lc' als)::EC) Mem0), trace_nil)
      end
    | insn_unreachable _ => None
    end

  | c::cs => (* non-terminator *)
    match c with
    | insn_bop id0 bop0 sz0 v1 v2 => 
      do gv3 <- BOP TD lc gl bop0 sz0 v1 v2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) 
              als)::EC) Mem0), trace_nil)         
    | insn_fbop id0 fbop0 fp0 v1 v2 => 
      do gv3 <- FBOP TD lc gl fbop0 fp0 v1 v2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) 
              als)::EC) Mem0), trace_nil)         
    | insn_extractvalue id0 t v idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- extractGenericValue TD t gv idxs;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv')
               als)::EC) Mem0), trace_nil)
    | insn_insertvalue id0 t v t' v' idxs =>
      do gv <- getOperandValue TD v lc gl;
      do gv' <- getOperandValue TD v' lc gl;
      do gv'' <- insertGenericValue TD t gv idxs t' gv';
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv'') 
              als)::EC) Mem0), trace_nil)
    | insn_malloc id0 t v0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      do gn <- getOperandValue TD v0 lc gl;
      match (malloc TD Mem0 tsz gn align0) with
      | None => None
      | Some (Mem', mb) =>
        ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 
               ($ (blk2GV TD mb) # (typ_pointer t) $)) als)::EC) Mem'),
            trace_nil)
      end
    | insn_free fid t v =>
      do mptr <- getOperandValue TD v lc gl;
      do Mem' <- free TD Mem0 mptr;
         ret ((mkState ((mkEC F B cs tmn lc als)::EC) Mem'), trace_nil)
    | insn_alloca id0 t v0 align0 =>
      do tsz <- getTypeAllocSize TD t;
      do gn <- getOperandValue TD v0 lc gl;
      match (malloc TD Mem0 tsz gn align0) with
      | None => None
      | Some (Mem', mb) =>
          ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 
                 ($ (blk2GV TD mb) # (typ_pointer t) $)) 
                 (mb::als))::EC) Mem'),
               trace_nil)
      end
    | insn_load id0 t v align0 =>
      do mp <- getOperandValue TD v lc gl;
      do gv <- mload TD Mem0 mp t align0;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 
                ($ gv # t $)) als)
              ::EC) Mem0), trace_nil)
    | insn_store sid t v1 v2 align0 =>
      do gv1 <- getOperandValue TD v1 lc gl;
      do mp2 <- getOperandValue TD v2 lc gl;
      do Mem' <- mstore TD Mem0 mp2 t gv1 align0;
         ret ((mkState ((mkEC F B cs tmn lc als)::EC) Mem'), trace_nil)
    | insn_gep id0 inbounds0 t v idxs =>
      do mp <- getOperandValue TD v lc gl;
      do vidxs <- values2GVs TD idxs lc gl;
      do mp' <- GEP TD t mp vidxs inbounds0;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 mp') 
               als)::EC) Mem0), trace_nil)
    | insn_trunc id0 truncop0 t1 v1 t2 =>
      do gv2 <- TRUNC TD lc gl truncop0 t1 v1 t2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2)
               als)::EC) Mem0), trace_nil)
    | insn_ext id0 extop0 t1 v1 t2 =>
      do gv2 <- EXT TD lc gl extop0 t1 v1 t2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2)
               als)::EC) Mem0), trace_nil)
    | insn_cast id0 castop0 t1 v1 t2 =>
      do gv2 <- CAST TD lc gl castop0 t1 v1 t2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv2) 
               als)::EC) Mem0), trace_nil)

    | insn_icmp id0 cond0 t v1 v2 =>
      do gv3 <- ICMP TD lc gl cond0 t v1 v2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) 
               als)::EC) Mem0), trace_nil)
    | insn_fcmp id0 fcond0 fp v1 v2 =>
      do gv3 <- FCMP TD lc gl fcond0 fp v1 v2;
         ret ((mkState ((mkEC F B cs tmn (updateAddAL _ lc id0 gv3) 
               als)::EC) Mem0), trace_nil)
    | insn_select id0 v0 t v1 v2 =>
      do cond0 <- getOperandValue TD v0 lc gl;
      do gv1 <- getOperandValue TD v1 lc gl;
      do gv2 <- getOperandValue TD v2 lc gl;
         ret ((mkState ((mkEC F B cs tmn 
                (if isGVZero TD cond0 then updateAddAL _ lc id0 gv2 
                 else updateAddAL _ lc id0 gv1) als)::EC) Mem0),
             trace_nil)  
    | insn_call rid noret0 tailc0 ft fv lp =>
      (* only look up the current module for the time being, 
         do not support linkage. *)
      do fptr <- getOperandValue TD fv lc gl;
      do fid <- OpsemAux.lookupFdefViaGVFromFunTable fs fptr;
      match (lookupFdefViaIDFromProducts Ps fid) with
      | None => 
        match (lookupFdecViaIDFromProducts Ps fid) with
        | None => None
        | Some (fdec_intro (fheader_intro fa rt' fid' la va)) =>
          if id_dec fid fid' then
            do gvs <- params2GVs TD lp lc gl;
              match (OpsemAux.callExternalFunction Mem0 fid gvs)
              with
              | Some (oresult, Mem1) =>
                do lc' <- exCallUpdateLocals TD ft noret0 rid oresult lc;
                ret ((mkState ((mkEC F B cs tmn lc' als)::EC) Mem1),
                     trace_nil)
              | None => None
              end
          else None
        end
      | Some (fdef_intro (fheader_intro fa rt fid' la va) lb) =>
        if id_dec fid fid' then
            match (getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb))
              with
            | None => None
            | Some (block_intro l' ps' cs' tmn') =>
                do gvs <- params2GVs TD lp lc gl;
                do lc0 <- initLocals TD la gvs;
                ret ((mkState ((mkEC (fdef_intro 
                      (fheader_intro fa rt fid la va) lb) 
                      (block_intro l' ps' cs' tmn') cs' tmn' lc0 
                      nil)::
                    (mkEC F B ((insn_call rid noret0 tailc0 ft fv lp)::cs) tmn 
                      lc als)::EC) Mem0),
                    trace_nil)
            end
        else None
      end
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

Ltac dos_simpl := simpl; repeat dgvs_instantiate_inv; repeat dos_rewrite.

Lemma dsInsn__implies__interInsn : forall cfg state state' tr,
  sInsn cfg state state' tr ->
  interInsn cfg state = Some (state', tr).
Proof. 
  intros cfg state state' tr HdsInsn.
  Opaque malloc GEP. 
  (sInsn_cases (destruct HdsInsn) Case); dos_simpl; auto.
  Case "sCall".
    apply lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [J1 J2]].
    rewrite J1. simpl.
    rewrite J2. 
    apply lookupFdefViaIDFromProducts_ideq in J2; subst; auto.
    destruct (id_dec fid fid); try congruence.
    destruct lb; inv H2.
    rewrite H4. simpl. auto.
  Case "sExCall".
    apply lookupExFdecViaPtr_inversion in H1.
    destruct H1 as [fn [J1 [J2 J3]]].
    rewrite J1. simpl.
    rewrite J2. rewrite J3.
    apply lookupFdecViaIDFromProducts_ideq in J3; subst; auto.
    destruct (id_dec fid fid); try congruence.
    rewrite H4. rewrite H5. simpl. auto.
Qed.

Lemma interInsn__implies__dsInsn : forall cfg state state' tr,
  interInsn cfg state = Some (state', tr) ->
  sInsn cfg state state' tr.
Proof.
  intros cfg state state' tr HinterInsn.
  destruct cfg. destruct state.
  destruct ECS0; simpl in HinterInsn;
    try solve [inversion HinterInsn].

    destruct e as [F B cs tmn lc als].
    destruct cs.
      destruct tmn.
      Case "insn_return".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas CurTargetData0 Mem0 als) as R2.
            destruct R1; try solve [inversion HinterInsn].
            destruct R2; try solve [inversion HinterInsn]. 
            simpl in HinterInsn.
            remember (returnUpdateLocals CurTargetData0 c v lc lc' Globals0)
              as R3.
            destruct R3; inversion HinterInsn; subst; eauto.

      Case "insn_return_void".
        destruct ECS0;
          try solve [inversion HinterInsn].
          
          destruct e as [F' B' cs' tmn' lc' als'].
          destruct cs';
            try solve [inversion HinterInsn].

            remember (Instruction.isCallInst c) as R1.
            remember (free_allocas CurTargetData0 Mem0 als) as R2.
            remember (getCallerReturnID c) as R3.
            destruct R1; try solve [inversion HinterInsn].
            destruct R3; try solve [inversion HinterInsn].
            destruct R2; inversion HinterInsn; subst; eauto.

      Case "insn_br".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; try solve [inversion HinterInsn].
          simpl in HinterInsn.
          remember (isGVZero CurTargetData0 g) as R3.
          destruct R3.
            remember (lookupBlockViaLabelFromFdef F l1) as R2.
            destruct R2; tinv HinterInsn.
              destruct b.
              remember (switchToNewBasicBlock CurTargetData0
                (block_intro l2 p c t) B Globals0 lc) as R4.
              destruct R4; inv HinterInsn.              
              eapply sBranch; simpl; eauto.
                rewrite <- HeqR3. auto.
        
            remember (lookupBlockViaLabelFromFdef F l0) as R2.
            destruct R2; inversion HinterInsn; subst.
              destruct b.
              remember (switchToNewBasicBlock CurTargetData0
                (block_intro l2 p c t) B Globals0 lc) as R4.
              destruct R4; inv HinterInsn.
              eapply sBranch; simpl; eauto.    
                rewrite <- HeqR3. auto.

      Case "insn_br_uncond".
        remember (lookupBlockViaLabelFromFdef F l0) as R2.
        destruct R2; inversion HinterInsn; subst.
          destruct b.
          remember (switchToNewBasicBlock CurTargetData0
            (block_intro l1 p c t) B Globals0 lc) as R3.
          destruct R3; inversion HinterInsn; subst.
          inversion HinterInsn; subst; eauto.

      Case "insn_unreachable".
        inversion HinterInsn.
                    
      destruct c.
      Case "insn_bop".
        remember (BOP CurTargetData0 lc Globals0 b s v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.
          
      Case "insn_fbop".
        remember (FBOP CurTargetData0 lc Globals0 f f0 v v0) as R1.
        destruct R1; 
          simpl in HinterInsn;
          inversion HinterInsn; subst; eauto.

      Case "insn_extractvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (extractGenericValue CurTargetData0 t g l0) as R2.
        destruct R2; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_insertvalue".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (insertGenericValue CurTargetData0 t g l0 t0 g0) as R3.
        destruct R3; simpl in HinterInsn; inv HinterInsn; eauto.
          
      Case "insn_malloc".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn]. 
        remember (getOperandValue CurTargetData0 v lc Globals0) as R3.
        destruct R3; simpl in HinterInsn;
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 s g a) as R2.
        destruct R2; tinv HinterInsn.
        destruct p; inv HinterInsn; subst; eauto.
    
      Case "insn_free".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (free CurTargetData0 Mem0 g) as R2.
        destruct R2; simpl in HinterInsn; inv HinterInsn; eauto.
          
      Case "insn_alloca".
        remember (getTypeAllocSize CurTargetData0 t) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v lc Globals0) as R3.
        destruct R3; simpl in HinterInsn;
          try solve [inversion HinterInsn].         
        remember (malloc CurTargetData0 Mem0 s g a) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        destruct p; inversion HinterInsn; subst; eauto.
          
      Case "insn_load".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mload CurTargetData0 Mem0 g t a) as R2.
        destruct R2; simpl in HinterInsn; inv HinterInsn; eauto.
          
      Case "insn_store".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (mstore CurTargetData0 Mem0 g0 t g a) as R3.
        destruct R3; simpl in HinterInsn; inv HinterInsn; eauto.
          
      Case "insn_gep".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (values2GVs CurTargetData0 l0 lc Globals0) as R3.
        destruct R3; simpl in HinterInsn; try solve [inversion HinterInsn].     
        remember (GEP CurTargetData0 t g l1 i1) as R2.
        destruct R2; simpl in HinterInsn; inv HinterInsn; 
          eauto using dos_in_list_gvs_intro.

      Case "insn_trunc".
        remember (TRUNC CurTargetData0 lc Globals0 t t0 v t1) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_ext".
        remember (EXT CurTargetData0 lc Globals0 e t v t0) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_cast".
        remember (CAST CurTargetData0 lc Globals0 c t v t0) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_icmp".
        remember (ICMP CurTargetData0 lc Globals0 c t v v0) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_fcmp".
        remember (FCMP CurTargetData0 lc Globals0 f f0 v v0) as R.
        destruct R; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_select".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R1.
        destruct R1; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v0 lc Globals0) as R2.
        destruct R2; simpl in HinterInsn; 
          try solve [inversion HinterInsn].         
        remember (getOperandValue CurTargetData0 v1 lc Globals0) as R3.
        destruct R3; simpl in HinterInsn; inv HinterInsn; eauto.

      Case "insn_call".
        remember (getOperandValue CurTargetData0 v lc Globals0) as R0.
        destruct R0; try solve [inversion HinterInsn]. simpl in HinterInsn.
        remember (lookupFdefViaGVFromFunTable FunTable0 g) as R4.
        destruct R4; try solve [inversion HinterInsn]. simpl in HinterInsn.
        remember (lookupFdefViaIDFromProducts CurProducts0 i1) as R1.
        destruct R1; simpl in HinterInsn.
          destruct f. destruct f.
          destruct (id_dec i1 i2); try solve [inversion HinterInsn]; subst.
          destruct b; try solve [inversion HinterInsn].
          destruct b.
          remember (params2GVs CurTargetData0 p lc Globals0) as R10.
          destruct R10; try solve [inversion HinterInsn]. simpl in HinterInsn.
          remember (initLocals CurTargetData0 a l1) as R11. 
          destruct R11; inv HinterInsn.
          eapply sCall; eauto.
            unfold lookupFdefViaPtr.
            rewrite <- HeqR4. simpl. auto.
        
          remember (lookupFdecViaIDFromProducts CurProducts0 i1) as R2.
          destruct R2; simpl in HinterInsn;
            try solve [inversion HinterInsn].
            destruct f. destruct f.
            destruct (id_dec i1 i2); try solve [inversion HinterInsn]; subst.
            remember (params2GVs CurTargetData0 p lc Globals0) as R5.
            destruct R5; try solve [inversion HinterInsn]; subst.
            simpl in HinterInsn.
            remember (callExternalFunction Mem0 i2 l0) as R3.
            destruct R3 as [[oresult Mem1]|]; tinv HinterInsn.
            remember (exCallUpdateLocals CurTargetData0 t n i0 oresult lc) as R4.
            destruct R4; inv HinterInsn.
            eapply sExCall; eauto using dos_in_list_gvs_intro.
              unfold lookupExFdecViaPtr.
              rewrite <- HeqR4. simpl. rewrite <- HeqR1. eauto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


