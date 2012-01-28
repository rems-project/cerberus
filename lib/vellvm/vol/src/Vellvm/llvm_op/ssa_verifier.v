Add LoadPath "../ott".
Add LoadPath "../monads".
Add LoadPath "../compcert".
Add LoadPath "../../../../theory/metatheory_8.3".
Add LoadPath "../".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import ListSet.
Require Import monad.
Require Import Logic_Type.
Require Import Arith.
Require Import Bool.
Require Import Compare_dec.
Require Import Metatheory.
Require Import ssa_analysis.

Module LLVMverifier.

Export LLVMsyntax.
Export LLVMlib.


(* defns Jwf_typ *)
Inductive wf_typ : typ -> Prop :=    (* defn wf_typ *)
 | wf_typ_int : forall (N5:nat),
     wf_typ (typ_int N5)
 | wf_typ_metadate : 
     wf_typ typ_metadata
 | wf_typ_function : forall (typ_list:list_typ) (typ_5:typ),
     isValidReturnTyp typ_5 ->
     wf_typ typ_5 ->
     (forall typ_, In typ_ (unmake_list_typ typ_list) -> (isValidArgumentTyp typ_)) ->
     (forall typ_, In typ_ (unmake_list_typ typ_list) -> (wf_typ typ_)) ->
     wf_typ (typ_function typ_5 typ_list).

(* defns Jwf_operand_insn *)
Definition wf_operand_insn (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)
                           (insn5 op:insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  {{{
  do id' <- ret (getInsnID  op);
  do OpBlock <- (lookupBlockViaIDFromFdef fdef5 id');

     (* Check that a definition dominates all of its uses *)
     (*
     If (isInvokeInsnB op)
     then 
     (* Invoke results are only usable in the normal destination, not in the
        exceptional destination. *)
     do ln <- getNormalDestFromInvokeInsnC op;
     do NormalDest <- lookupBlockViaLabelFromSystem system5 ln;
     do lu <- getUnwindDestFromInvokeInsnC op;
     do UnwindDest <- lookupBlockViaLabelFromSystem system5 lu;
     do Assert (not (NormalDest = UnwindDest));

     (* PHI nodes differ from other nodes because they actually "use" the
        value in the predecessor basic blocks they correspond to. *)
     do UseBlock <- 
        If (isPhiNodeB insn5) 
        then 
        do l <- getLabelViaIDFromPhiNode insn5 id';
           lookupBlockViaLabelFromSystem system5 l
        else
           ret block5
        endif;

        If (isPhiNodeB insn5 && (UseBlock =b= OpBlock))
        then
        (* Special case of a phi node in the normal destination or the unwind
           destination *)
           Assert (block5 = NormalDest /\ isReachableFromEntry fdef5 UseBlock)
        else
        (* Invoke result does dominate all uses! *)
        do Assert (blockDominates dt5 NormalDest UseBlock \/ 
                ~ (isReachableFromEntry fdef5 UseBlock));

        (* If the normal successor of an invoke instruction has multiple
           predecessors, then the normal edge from the invoke is critical,
           so the invoke value can only be live if the destination block
           dominates all of it's predecessors (other than the invoke). *)
           If (negb (hasSinglePredecessor NormalDest usedef_block5) &&
               (isReachableFromEntryB fdef5 UseBlock)
              )
           then
           (* If it is used by something non-phi, then the other case is that
              'NormalDest' dominates all of its predecessors other than the
              invoke.  In this case, the invoke value can still be used. *)
             for PI in (predOfBlock NormalDest usedef_block5) do
               (* Invoke result must dominate all uses! *)
               If (insnHasParent op system5)
               then
               do parentOfOp <- getParentOfInsnFromSystemC op system5;
                  If (negb (blockDominatesB dt5 NormalDest PI) && 
                      isReachableFromEntryB fdef5 PI)
                  then ret False
                  endif
               endif
             endfor
           endif
        endif
     *)
     If (isPhiNodeB insn5)
     then
     (* PHI nodes are more difficult than other nodes because they actually
        "use" the value in the predecessor basic blocks they correspond to. *)
     do predl <- getLabelViaIDPhiNode insn5 id';
     do PredBB <- lookupBlockViaLabelFromSystem system5 predl;
        (* Instruction must dominate all uses! *) 
        Assert (blockDominates fdef5 OpBlock PredBB \/ ~ isReachableFromEntry fdef5 PredBB)
     else       
     (* 
        LLVM uses InstsInThisBlock to remember checked insns within the currren block,
        such that it doesn't need to call DT (that is costly) every time. And LLVM also
        optimizes it when OpBlock = BB:

        if (OpBlock == BB) {
          // If they are in the same basic block, make sure that the definition
          // comes before the use.
          Assert2(InstsInThisBlock.count(Op) || !DT->isReachableFromEntry(BB),
                  "Instruction does not dominate all uses!", Op, &I);
        }

        // Definition must dominate use unless use is unreachable!
        Assert2(InstsInThisBlock.count(Op) || DT->dominates(Op, &I) ||
                !DT->isReachableFromEntry(BB),
                "Instruction does not dominate all uses!", Op, &I);

        But we don't do this in Coq, and check Dominance everytime.
     *)
        (* Definition must dominate use unless use is unreachable! *)
        Assert (insnDominates op insn5 block5 \/ ~ isReachableFromEntry fdef5 block5)
     endif
  }}}.

(* defns Jwf_operand *)
Definition wf_operand (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef5:fdef)
                            (block5:block)
                            (insn5:insn) 
                            (id':id): Prop :=
  let '((module_intro list_layout5 namedts5 list_product5), (usedef_insn5, usedef_block5)) := module_info5 in
  {{{
  do ret (insnInSystemModuleIFdefBlockB
            insn5 
            system5  
            ( (module_intro list_layout5 namedts5 list_product5) , ( usedef_insn5 ,  usedef_block5 )) 
            fdef5   
            block5);
  do ids5 <- ret (getInsnOperands insn5);
  do ret ( set_In  id' ids5 );

  do id_binding' <- ret (lookupBindingViaIDFromSystem system5 id');
  (* Check to make sure that only first-class-values are operands to instructions. *)
  do typ' <- (getBindingTyp id_binding');
  do Assert (isFirstClassTyp typ');
  
  (* Valid use of metadata pointer. *)
  do If (isPointerTypB typ')
     then 
     do typ'' <- (getPointerEltTyp typ');
        Assert (not (typEqB typ'' typ_metadata))
     endif;

  do If (isBindingFdecB id_binding')
     then
     do fdec5 <- (getBindingFdec id_binding');
     (* Check to make sure that the "address of" an intrinsic function is never
        taken *)
     do id0 <- ret (getFdecID fdec5);
     do Assert (( ~ set_In id0 intrinsic_funs5) \/  getCalledValueID insn5 = Some id0);

     (* Referencing function exists in current module *)
        Assert (In  (product_fdec fdec5) list_product5)
     endif;

  do If (isBindingArgB id_binding')
     then 
     do arg <- getBindingArg id_binding';
     (* Referring to an argument in the current function *)
        ret (argInFdefB arg fdef5=true)
     endif;

  do If (isBindingGvarB id_binding')
     then 
     (* Referencing global in the current module *)
     do g <- getBindingGvar id_binding';
        ret True
     endif;

  do If (isBindingInsnB id_binding')
     then 
     (*  Check when id_binding' is insn *)
     do insn' <- getBindingInsn id_binding';
        ret (wf_operand_insn intrinsic_funs5 system5 module_info5 fdef5 block5 insn5 insn')
     endif;

     ret True
  }}}.
  
(* defns Jwf_label *)
Inductive wf_label : intrinsic_funs -> system -> module_info -> fdef -> block -> insn -> l -> Prop :=    (* defn wf_label *)
 | wf_label_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_id) (usedef_block5:usedef_block) (fdef5:fdef) (block5:block) (insn5:insn) (l5:l) (ls5:ls),
     insnInSystemModuleIFdefBlockB insn5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))  fdef5   block5 = true ->
     getInsnLabels insn5 = ls5 ->
      ( set_In  l5   ls5 )  ->
      (lookupBlockViaLabelFromSystem  system5   l5  =   (Some  block5 )  )  ->
     blockInFdefB block5 fdef5 = true ->
     wf_label intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     fdef5   block5 insn5 l5.

(* defns JvisitInstruction *)
Definition visitInstruction (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (fdef5:fdef)
                            (block5:block)
                            (insn5:insn) : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  {{{
  (* Instruction must be embedded in basic block! *)
  do ret (insnInSystemModuleIFdefBlockB 
            insn5   
            system5   
            ( module5 , ( usedef_insn5 ,  usedef_block5 ))     
            fdef5
            block5);

  (* Check that non-phi nodes are not self referential *)
  do If (isPhiNodeB insn5)
     then 
     do id5 <- ret (getInsnID insn5);
        for id5' in (getIdUseDef usedef_insn5 id5) do
          Assert ((not (id5 = id5')) \/ 
                  (not (isReachableFromEntry fdef5 block5)))
        endfor
     endif;

  (* Verify that if this is a terminator that it is at the end of the block. *)

  (* Check that void typed values don't have names 
     We dont need to check this in Coq. *)

  (* Check that the return value of the instruction is either void or a legal
     value type. *)
  do typ5 <- (getInsnTyp insn5);
  do Assert (typEqB typ5 typ_void  \/  isFirstClassTyp typ5);

  (* Check that the instruction doesn't produce metadata or metadata*. Calls
     all already checked against the callee type. *)
  do Assert ((not (typEqB typ5 typ_metadata ))   \/  
             (*isInvokeInsn insn5   \/  *)
             isCallInsnB insn5 = true );

  (* Instructions may not produce pointer to metadata *)
  do If (isPointerTypB typ5 )
     then  
     do typ' <- (getPointerEltTyp typ5);
        Assert (not (typEqB typ' typ_metadata ))
     endif;

  (* Check that all uses of the instruction, if they are instructions
     themselves, actually have parent basic blocks.  If the use is not an
     instruction, it is an error!
     We should prove a lemma for this later *)
  
  (* Check operands *)
  do for insn in (getInsnOperands insn5) do
     (* Check to make sure that only first-class-values are operands to
        instructions. *)
       ret (wf_operand intrinsic_funs5 system5 module_info5 fdef5 block5 insn5 insn)
     endfor;

  (* Check labels *)
     for l in (getInsnLabels insn5) do
       ret (wf_label intrinsic_funs5 system5 module_info5 fdef5 block5 insn5 l)
     endfor
  }}}.

(* defns JvisittTerminatorInst *)
Definition visitTerminatorInst (intrinsic_funs5:intrinsic_funs) 
                               (system5:system)
                               (module_info5:module_info)
                               (fdef5:fdef)
                               (block5:block)
                               (insn5:insn) : Prop :=
  (* Ensure that terminators only exist at the end of the basic block. *)
  {{{
     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef5 block5 insn5)
  }}}.

Definition visitReturnInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (RI:terminator)                              (* ReturnInst *)
                           : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let F := fdef5 in 
  {{{
  do N <- ret (ReturnInst.getNumOperands (insn_terminator RI));
  do If ((Function.getDefReturnType F) =t= typ_void)
     then
     (* return instr that returns non-void in Function cannot be of void return type! *)
       Assert (N =n= 0)
     elseif ((N =n= 1) && (ReturnInst.hasReturnType RI))
     then
     do rt <- ReturnInst.getReturnType RI;
     (* Exactly one return value and it matches the return type. Good. *)
        Assert ((Function.getDefReturnType F) =t= rt)
     elseif (false)
     then
     (*
       else if (const StructType *STy = dyn_cast<StructType>(F->getReturnType())) {
       // The return type is a struct; check for multiple return values.
       Assert2(STy->getNumElements() == N,
               "Incorrect number of return values in ret instruction!",
                &RI, F->getReturnType());
       for (unsigned i = 0; i != N; ++i)
         Assert2(STy->getElementType(i) == RI.getOperand(i)->getType(),
                 "Function return type does not match operand "
                 "type of return inst!", &RI, F->getReturnType());
     *)
       ret True
     (* The support for multiple return values is already absolete.
     elseif (isArrayTypB (Function.getDefReturnType F))
     then
     do ATy <- ret (Function.getDefReturnType F);
     (* The return type is an array; check for multiple return values. *)
     do Assert ((ArrayType.getNumElements ATy) =n= N);
        for i from 0 to N do
        (* Function return type matches operand type of return inst! *)
        do et <- (ArrayType.getElementType ATy);
        do rt <- (ReturnInst.getReturnType RI); 
        (* !! FIXME: RI.getOperand(i)->getType() *)
           Assert (et =t= rt)
        endfor
     *)
     else
     (* Function return type does not match operand type of return inst! *)
        ret False
     endif;

  (* Check to make sure that the return value has necessary properties for
     terminators... *)
     ret (visitTerminatorInst intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_terminator RI))
  }}}.

Definition verifyCallSite (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (CS:cmd)                              (* CallSite *)
                           : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let F := fdef5 in 
  {{{
  do I <- ret CS;
  (* LLVM checks that 
       "Called function must be a pointer!"
       "Called function is not pointer to function type!"
     We don't need to check this, but only ensure Call and FTy are valid
     *)
  (*
  do Call <- CallSite.getCalledFunction CS system5;
  do FTy <- ret CallSite.getFdefTyp Call;
  *)

  (* Verify that the correct number of arguments are being passed 
     not supporing variant arguments *)
  (*
  do 
     If (FunctionType.isVarArg FTy)
     then 
     (* Called function requires less parameters. *)
     do numParams <- (FunctionType.getNumParams FTy);
        Assert(CallSite.arg_size Call >= numParams)
     else
     (* Correct number of arguments passed to called function! *)
     do numParams <- (FunctionType.getNumParams FTy);     
        Assert(CallSite.arg_size Call =n= numParams)   
     endif;
  *)
  (*
  do numParams <- (FunctionType.getNumParams FTy);     
  do Assert(CallSite.arg_size Call =n= numParams);
  *)

  (* Verify that all arguments to the call match the function type... *)
  (*
  do numParams <- (FunctionType.getNumParams FTy);
  do for i From 0 to numParams do
     (* Call parameter type should match function signature. *)
       do argt <- CallSite.getArgumentType Call i;
       do part <- FunctionType.getParamType FTy i;
          Assert (argt =t= part)
     endfor;
  *)

  (* Will Verify call attributes later... *)

  (* Verify that there's no metadata unless it's a direct call to an intrinsic. 
     Open soooon... *)

     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_cmd CS))
  }}}.  


Definition visitCallInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (CI:cmd)                              (* CallInst *)
                           : Prop :=
(*
  if (Function *F = CI.getCalledFunction())
    if (Intrinsic::ID ID = (Intrinsic::ID)F->getIntrinsicID())
      visitIntrinsicFunctionCall(ID, CI);
*)
  verifyCallSite intrinsic_funs5 system5 module_info5 fdef5 block5 CI.


Definition visitInvokeInst (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (II:cmd)                              (* InvokeInst *)
                           : Prop :=
  verifyCallSite intrinsic_funs5 system5 module_info5 fdef5 block5 II.

Definition visitBinaryOperator (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (B:cmd)                              (* BinaryOperator *)
                           : Prop :=
  {{{
  (* "Both operands to a binary operator are of the same type" *)
  do firstT <- BinaryOperator.getFirstOperandType system5 B;
  do secondT <- BinaryOperator.getSecondOperandType system5 B;
  do Assert (firstT =t= secondT);

  (* Check that integer arithmetic operators are only used with
     integral operands. *)
  do rT <- BinaryOperator.getResultType B;
  (* Integer arithmetic operators only work with integral types *)
  do Assert (Typ.isIntOrIntVector rT);
  (* Integer arithmetic operators must have same type for operands and result *)
  do Assert (rT =t= firstT);

     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_cmd B))
  }}}.  

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
  (length (lookupIdsViaLabelFromIdls idls0 l) <= 1) /\
  (_checkIdenticalIncomingValues idls' idls0)
end.

Definition checkIdenticalIncomingValues (PN:phinode) : Prop :=
match PN with
| insn_phi _ _ idls => _checkIdenticalIncomingValues idls idls
end.

Definition visitPHINode (intrinsic_funs5:intrinsic_funs) 
                           (system5:system)
                           (module_info5:module_info)
                           (fdef5:fdef)
                           (block5:block)                              
                           (PN:phinode)                              (* PHINode *)
                           : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  let F := fdef5 in 
  {{{
  (* Ensure that the PHI nodes are all grouped together at the top of the block.
     This can be tested by checking whether the instruction before this is
     either nonexistent (because this is begin()) or is a PHI node.  If not,
     then there is some other instruction before a PHI. *)
  (* This checking is easier than the one in LLVM *)

  (* The following properties 1-4 are checked in visitBlock by LLVM,
     but we check them here. *)
  (* 1 Ensure that PHI nodes have at least one entry! *)
  do nIncomingValues <- ret (PHINode.getNumIncomingValues PN);
  do Assert (nIncomingValues >0);

  (* 2 PHINode should have one entry for each predecessor of its 
     parent basic block! *)
  do preds <- ret (predOfBlock block5 usedef_block5);
  do preds_size <- ret (length preds);
  do Assert (nIncomingValues =n= preds_size);

  (* 3 Check to make sure that the predecessors and PHI node entries are
     matched up. *)
  do ls1 <- ret (getLabelsFromBlocks preds);
  do ls2 <- ret (getLabelsFromPhiNode PN);
  do Assert (lset_eq ls1 ls2);

  (* 4 Check to make sure that if there is more than one entry for a
     particular basic block in this PHI node, that the incoming values are
     all identical. *)
  do Assert (checkIdenticalIncomingValues PN);

  (* Check that all of the operands of the PHI node have the same type as the
     result. *)
  do for i From 0 to nIncomingValues do
     do rT <- getInsnTyp (insn_phinode PN);
     do iT <- PHINode.getIncomingValueType system5 PN i;
        Assert (rT =t= iT)
     endfor;

  (* All other PHI node constraints are checked in the visitBasicBlock method. *)
     ret (visitInstruction intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_phinode PN))
  }}}. 

(* defns Jwf_insn *)
Inductive wf_insn : intrinsic_funs -> system -> module_info -> fdef -> block -> insn -> Prop :=    (* defn wf_insn *)
 | wf_insn_return : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (block5:block) rid (typ5:typ) (value5:value),
     visitReturnInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_return rid typ5 value5) ->
     wf_insn intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_terminator (insn_return rid typ5 value5))
(*
 | wf_insn_return_void : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (dt5:dt) (block5:block),
     visitReturnInst intrinsic_funs5 system5 module_info5   fdef5   block5 insn_return_void ->
     wf_insn intrinsic_funs5 system5 module_info5   fdef5   block5 insn_return_void
*)
 | wf_insn_br : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (block5:block) bid (value5:value) (l1 l2:l) (fdef5:fdef) ,
     visitTerminatorInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_terminator (insn_br bid value5 l1 l2)) ->
     wf_insn intrinsic_funs5 system5   module_info5  fdef5 block5 (insn_terminator (insn_br bid value5 l1 l2))
 | wf_insn_br_uncond : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (block5:block) (bid l5:l) (module_info5:module_info) (fdef5:fdef),
     visitTerminatorInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_terminator (insn_br_uncond bid l5)) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_terminator (insn_br_uncond bid l5))
(*
 | wf_insn_invoke : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (block5:block) (id_5:id) (typ0:typ) (id0:id) (list_param5:list_param) (l1 l2:l) (module_info5:module_info) (fdef5:fdef) (dt5:dt),
     visitInvokeInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_invoke id_5 typ0 id0 list_param5 l1 l2) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_invoke id_5 typ0 id0 list_param5 l1 l2)
*)
 | wf_insn_call : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (block5:block) (id_5:id) (typ0:typ) (v0:value) (list_param5:params) (module_info5:module_info) (fdef5:fdef) ,
     visitCallInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_call id_5 false false typ0 v0 list_param5) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_cmd (insn_call id_5 false false typ0 v0 list_param5))
 | wf_insn_unreachable : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (fdef5:fdef) (block5:block) (module_info5:module_info) (fdef5:fdef)  bid,
     visitTerminatorInst intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_terminator (insn_unreachable bid)) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_terminator (insn_unreachable bid))
 | wf_insn_add : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (fdef5:fdef) (block5:block) (id5:id) (sz5:nat) (value1 value2:value) (module_info5:module_info) (fdef5:fdef) ,
     visitBinaryOperator intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_bop id5 bop_add sz5 value1 value2) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_cmd (insn_bop id5 bop_add sz5 value1 value2))
 | wf_insn_phi : forall (id_l_list:list_value_l) (intrinsic_funs5:intrinsic_funs) (system5:system) (fdef5:fdef) (block5:block) (id_5:id) (typ5:typ) (module_info5:module_info) (fdef5:fdef) ,
     visitPHINode intrinsic_funs5 system5 module_info5   fdef5   block5 (insn_phi id_5 typ5 id_l_list) ->
     wf_insn intrinsic_funs5 system5   module_info5   fdef5 block5 (insn_phinode (insn_phi id_5 typ5 id_l_list))
 .

Inductive wf_list_cmd : intrinsic_funs -> system -> module_info -> fdef -> block -> cmds -> Prop :=  
 | wf_list_cmd_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (block5:block),
     wf_list_cmd intrinsic_funs5 system5 module_info5 fdef5 block5  nil 
 | wf_list_cmd_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (block5:block) (list_cmd5:cmds) (cmd5:cmd),
     wf_insn intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_cmd cmd5) ->
     wf_list_cmd intrinsic_funs5 system5 module_info5 fdef5 block5 list_cmd5 ->
     wf_list_cmd intrinsic_funs5 system5 module_info5 fdef5 block5  ( cmd5 :: list_cmd5 ) .

Inductive wf_list_phinode : intrinsic_funs -> system -> module_info -> fdef -> block -> phinodes -> Prop :=  
 | wf_list_phinode_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (block5:block),
     wf_list_phinode intrinsic_funs5 system5 module_info5 fdef5 block5  nil 
 | wf_list_phinode_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (block5:block) (list_phinode5:phinodes) (phinode5:phinode),
     wf_insn intrinsic_funs5 system5 module_info5 fdef5 block5 (insn_phinode phinode5) ->
     wf_list_phinode intrinsic_funs5 system5 module_info5 fdef5 block5 list_phinode5 ->
     wf_list_phinode intrinsic_funs5 system5 module_info5 fdef5 block5  ( phinode5 :: list_phinode5 ) .


(* verifyBasicBlock - Verify that a basic block is well formed... *)
Inductive verifyBasicBlock : intrinsic_funs -> system -> module_info -> fdef -> block -> Prop :=    (* defn wf_block *)
 | verifyBasicBlock_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (l5:l) list_phinode5 (list_cmd5:cmds) terminator5,
     blockInSystemModuleIFdefB (block_intro l5 list_phinode5 list_cmd5 terminator5)  system5 module_info5 fdef5 = true ->

     wf_list_cmd intrinsic_funs5 system5 module_info5 fdef5 (block_intro l5 list_phinode5 list_cmd5 terminator5) list_cmd5 ->
     wf_list_phinode intrinsic_funs5 system5 module_info5 fdef5 (block_intro l5 list_phinode5 list_cmd5 terminator5) list_phinode5 ->
     wf_insn intrinsic_funs5 system5 module_info5 fdef5 (block_intro l5 list_phinode5 list_cmd5 terminator5) (insn_terminator terminator5) ->

    (* Ensure that the PHI nodes are all grouped together at the top of the block.
       This can be tested by checking whether the instruction before this is
       either nonexistent (because this is begin()) or is a PHI node.  If not,
       then there is some other instruction before a PHI.
       LLVM checks this only in visitPHINode, we pull it up to block checking. 
       It is easier than the one in LLVM::visitPHINode.
     *)
     
     (* Ensure that basic blocks have terminators! *)

     (* We moved some assertions to visitPhiNode *)

     verifyBasicBlock intrinsic_funs5 system5 module_info5 fdef5 (block_intro l5 list_phinode5 list_cmd5 terminator5).

(* defns Jwf_list_block *)
Inductive wf_list_block : intrinsic_funs -> system -> module_info -> fdef -> blocks -> Prop :=    (* defn wf_list_block *)
 | wf_list_block_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef),
     wf_list_block intrinsic_funs5 system5 module_info5 fdef5  nil 
 | wf_list_block_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef) (list_block5:blocks) (block5:block),
     verifyBasicBlock intrinsic_funs5 system5 module_info5 fdef5 block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef5 list_block5 ->
     wf_list_block intrinsic_funs5 system5 module_info5 fdef5  ( block5 :: list_block5 ) .

(* visitFunctionDef - Verify that a function def is ok. *)
Definition visitFunctionDef (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (F:fdef)
                            : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  {{{
  (* Check function arguments. *)
  do FT <- ret (Function.getDefFunctionType F);
  do NumArgs <- ret (Function.def_arg_size F);
  do NumParams <- FunctionType.getNumParams FT;

  (* Functions may not have common linkage *)
 
  (* Formal arguments must match # of arguments for function type! *)
  do Assert (NumArgs =n= NumParams);
  
  (* Functions cannot return aggregate values *)
  do rT <- ret (Function.getDefReturnType F);
  do Assert ((isFirstClassTypB rT) ||
             (rT =t= typ_void) ); (* or struct type *)

  (* "Invalid struct return type!" *)

  (* Attributes after last parameter! *)

  (* Check function attributes. *)

  (* Check that this function meets the restrictions on this calling convention. *)

  (* Function may not return metadata unless it's an intrinsic *)

  (* Check that the argument values match the function type for this function... *)
     (* Argument value does not match function argument type! *)
     (* Function arguments must have first-class types! *)
     (* Function takes metadata but isn't an intrinsic *)

  (* Verify that this function (which has a body) is not named "llvm.*".  It
     is not legal to define intrinsics. *)

  (* Check the entry node 
     Entry block to function must not have predecessors! *)
  do Entry <- getEntryOfFdef F;
  do preds <- ret (predOfBlock Entry usedef_block5);
     Assert (length preds = 0)
  }}}.

(* visitFunctionDec - Verify that a function dec is ok. *)
Definition visitFunctionDec (intrinsic_funs5:intrinsic_funs) 
                            (system5:system)
                            (module_info5:module_info)
                            (F:fdec)
                            : Prop :=
  let '(module5, (usedef_insn5, usedef_block5)) := module_info5 in
  {{{
  (* Check function arguments. *)
  do FT <- ret (Function.getDecFunctionType F);
  do NumArgs <- ret (Function.dec_arg_size F);
  do NumParams <- FunctionType.getNumParams FT;

  (* Functions may not have common linkage *)
 
  (* Formal arguments must match # of arguments for function type! *)
  do Assert (NumArgs =n= NumParams);
  
  (* Functions cannot return aggregate values *)
  do rT <- ret (Function.getDecReturnType F);
     Assert ((isFirstClassTypB rT) ||
             (rT =t= typ_void) ) (* or struct type *)

  (* "Invalid struct return type!" *)

  (* Attributes after last parameter! *)

  (* Check function attributes. *)

  (* Check that this function meets the restrictions on this calling convention. *)

  (* Function may not return metadata unless it's an intrinsic *)

  (* Check that the argument values match the function type for this function... *)
     (* Argument value does not match function argument type! *)
     (* Function arguments must have first-class types! *)
     (* Function takes metadata but isn't an intrinsic *)

  (* Verify that this function (which has a body) is not named "llvm.*".  It
     is not legal to define intrinsics. *)

  (* Check invalid linkage type for function declaration *)
  }}}.


(* defns Jwf_fdef *)
Inductive wf_fdef : intrinsic_funs -> system -> module_info -> fdef -> Prop :=    (* defn wf_fdef *)
 | wf_fdef_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_id) (usedef_block5:usedef_block) (fheader5:fheader) (list_block5:blocks) ,
     productInSystemModuleIB (product_fdef  (fdef_intro fheader5 list_block5) ) system5   ( module5 , ( usedef_insn5 ,  usedef_block5 )) = true  ->

     visitFunctionDef intrinsic_funs5 system5 ( module5 , ( usedef_insn5 ,  usedef_block5 )) (fdef_intro fheader5 list_block5) ->

     wf_list_block intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))     (fdef_intro fheader5 list_block5)   list_block5 ->
     wf_fdef intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   (fdef_intro fheader5 list_block5).

(* defns Jwf_fdec *)
Inductive wf_fdec : intrinsic_funs -> system -> module_info -> fdec -> Prop :=    (* defn wf_fdef *)
 | wf_fdec_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module5:module) (usedef_insn5:usedef_id) (usedef_block5:usedef_block) (fheader5:fheader) (list_block5:blocks) ,
     productInSystemModuleIB (product_fdef  (fdef_intro fheader5 list_block5) ) system5   ( module5 , ( usedef_insn5 ,  usedef_block5 )) = true  ->
     visitFunctionDec intrinsic_funs5 system5 ( module5 , ( usedef_insn5 ,  usedef_block5 )) (fdec_intro fheader5) ->
     wf_fdec intrinsic_funs5 system5   ( module5 , ( usedef_insn5 ,  usedef_block5 ))   (fdec_intro fheader5).

(* defns Jwf_prod *)
Inductive wf_prod : intrinsic_funs -> system -> module_info -> product -> Prop :=    (* defn wf_prod *)
 | wf_prod_function_dec : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdec5:fdec),
     wf_fdec intrinsic_funs5 system5 module_info5 fdec5 ->
     wf_prod intrinsic_funs5 system5 module_info5 (product_fdec fdec5)
 | wf_prod_function_def : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (fdef5:fdef),
     wf_fdef intrinsic_funs5 system5 module_info5 fdef5 ->
     wf_prod intrinsic_funs5 system5 module_info5 (product_fdef fdef5).

(* defns Jwf_prods *)
Inductive wf_prods : intrinsic_funs -> system -> module_info -> products -> Prop :=    (* defn wf_prods *)
 | wf_prods_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info),
     wf_prods intrinsic_funs5 system5 module_info5  nil 
 | wf_prods_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (module_info5:module_info) (list_product5:products) (product5:product),
     wf_prods intrinsic_funs5 system5 module_info5 list_product5 ->
     wf_prod intrinsic_funs5 system5 module_info5 product5 ->
     wf_prods intrinsic_funs5 system5 module_info5  ( product5 :: list_product5 ) .

(* defns Jwf_module *)
Inductive wf_module : intrinsic_funs -> system -> module -> Prop :=    (* defn wf_module *)
 | wf_module_intro : forall (intrinsic_funs5:intrinsic_funs) (system5:system) list_layout5 namedts5 (list_product5:products) (usedef_insn5:usedef_id) (usedef_block5:usedef_block),
     In  (module_intro list_layout5 namedts5 list_product5)   system5  ->
     genIdUseDef  (module_intro list_layout5 namedts5 list_product5)  = usedef_insn5  ->
     genBlockUseDef  (module_intro list_layout5 namedts5 list_product5)  = usedef_block5  ->
     wf_prods intrinsic_funs5 system5   (  (module_intro list_layout5 namedts5 list_product5)  , ( usedef_insn5 ,  usedef_block5 ))   list_product5 ->
     wf_module intrinsic_funs5 system5  (module_intro list_layout5 namedts5 list_product5) .

(* defns Jwf_list_module *)
Inductive wf_list_module : intrinsic_funs -> system -> modules -> Prop :=    (* defn wf_list_module *)
 | wf_list_module_nil : forall (intrinsic_funs5:intrinsic_funs) (system5:system),
     wf_list_module intrinsic_funs5 system5  nil 
 | wf_list_module_cons : forall (intrinsic_funs5:intrinsic_funs) (system5:system) (list_module5:modules) (module5:module),
     wf_module intrinsic_funs5 system5 module5 ->
     wf_list_module intrinsic_funs5 system5 list_module5 ->
     wf_list_module intrinsic_funs5 system5  ( module5 :: list_module5 ) .

(* defns Jwf_system *)
Inductive wf_system : intrinsic_funs -> system -> Prop :=    (* defn wf_system *)
 | wf_system_intro : forall (intrinsic_funs5:intrinsic_funs) (list_module5:modules),
     wf_list_module intrinsic_funs5  list_module5  list_module5 ->
     uniqSystem  list_module5  ->
     wf_system intrinsic_funs5  list_module5 .

End LLVMverifier.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)


