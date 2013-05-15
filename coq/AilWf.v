Require Import Bool.
Require Import List.

Require Import AilSyntax AilTypingAux.

(* defns Jwf *)
Inductive wfTy : type -> Prop :=    (* defn wfTy *)
 | WfTyPointerObject : forall qs ty,
     wfNestedTy ty ->
     isObject ty ->
     wfTy (Pointer qs ty) 
 | WfTyPointerOther : forall qs ty ty',
     wfTy ty' ->
      ~ isObject ty ->
      ~ QualifierSet.In Restrict qs ->
     wfTy (Pointer qs ty)
 | WfTyBasicType : forall qs bt,
      ~ QualifierSet.In Restrict qs ->
     wfTy (Basic qs bt)
 | WfTyVoid : forall qs,
      ~ QualifierSet.In Restrict qs ->
     wfTy (Void qs)
 | WfTyArray : forall ty n,
     wfNestedTy ty ->
      ~ isIncomplete ty ->
     wfTy (Array ty n) 
 | WfTyFunction : forall ty_list ty,
     wfNestedTy ty ->
     (forall ty, In ty ty_list -> wfTy ty) ->
     (forall ty, In ty ty_list -> ~ isIncomplete ty) ->
     wfTy (Function ty ty_list)
with wfNestedTy : type -> Prop :=    (* defn wfNestedTy *)
 | WfNestedTyPointerObject : forall qs ty,
     wfTy ty ->
     isObject ty ->
     wfNestedTy (Pointer qs ty) 
 | WfNestedTyPointerOther : forall qs ty ty',
     wfTy ty' ->
      ~ isObject ty ->
      ~ QualifierSet.In  Restrict qs ->
     wfNestedTy (Pointer qs ty) 
 | WfNestedTyBasicType : forall qs bt,
      ~ QualifierSet.In Restrict qs ->
     wfNestedTy (Basic qs bt) 
 | WfNestedTyVoid : forall qs,
      ~ QualifierSet.In Restrict qs ->
     wfNestedTy (Void qs) 
with wfE : gamma -> sigma -> expression -> Prop :=    (* defn wfE *)
 | WfEUnary : forall G S op (e_l:expressionL),
     wfEL G S e_l ->
     wfE G S (ExpUnary op e_l) 
 | WfEBinary : forall G S eL1 op eL2,
     wfEL G S eL1 ->
     wfEL G S eL2 ->
     wfE G S (ExpBinary eL1 op eL2) 
 | WfEAssign : forall G S eL1 eL2,
     wfEL G S eL1 ->
     wfEL G S eL2 ->
     wfE G S (ExpAssign eL1 eL2) 
 | WfECompoundAssign : forall G S eL1 op eL2,
     wfEL G S eL1 ->
     wfEL G S eL2 ->
     wfE G S (ExpCompoundAssign eL1 op eL2) 
 | WfEConditional : forall G S eL1 eL2 eL3,
     wfEL G S eL1 ->
     wfEL G S eL2 ->
     wfEL G S eL3 ->
     wfE G S (ExpConditional eL1 eL2 eL3) 
 | WfECast : forall G S ty eL,
     wfTy ty ->
     wfEL G S eL ->
     wfE G S (ExpCast ty eL) 
 | WfECall : forall eL_list G S eL,
     (forall eL, In eL eL_list -> wfEL G S eL) ->
     wfE G S (ExpCall eL eL_list)
 | WfEConstant : forall G S n,
     wfE G S (ExpConstant n)
 | WfEVariable : forall G S v ty,
     (GammaMap.find v G = Some ty) ->
     wfE G S (ExpVariable v)
 | WfEFunction : forall G S v ty sL,
     (SigmaMap.find v S = Some (ty, sL)) ->
     wfE G S (ExpVariable v)
 | WfESizeOf : forall G S ty,
      ~ isIncomplete ty ->
      ~ isFunction ty ->
     wfE G S (ExpSizeof ty) 
 | WfEAlignOf : forall G S ty,
      ~ isIncomplete ty ->
      ~ isFunction ty ->
     wfE G S (ExpAlignof ty) 
with wfEL : gamma -> sigma -> expressionL -> Prop :=    (* defn wfEL *)
 | WfELDef : forall G S l e,
     wfE G S e ->
     wfEL G S (ExpLDef l e) 
with wfS : gamma -> sigma -> type -> bool -> statement -> Prop :=    (* defn wfS *)
 | WfSSkip : forall G S ty b,
     wfS G S ty b StmtSkip
 | WfSExp : forall G S ty b eL,
     wfEL G S eL ->
     wfS G S ty b (StmtExp eL) 
 | WfSBlock : forall sL_list G S ty b G',
     wfGamma G' ->
     (forall sL, In sL sL_list -> wfSL (GammaMap.update _ G' G) S ty b sL) ->
     wfS G S ty b (StmtBlock G' sL_list)
 | WfSIf : forall G S ty b eL sL1 sL2,
     wfEL G S eL ->
     wfSL G S ty b sL1 ->
     wfSL G S ty b sL2 ->
     wfS G S ty b (StmtIf eL sL1 sL2) 
 | WfSWhile : forall G S ty b eL sL,
     wfEL G S eL ->
     wfSL G S ty  true  sL ->
     wfS G S ty b (StmtWhile eL sL) 
 | WfSDo : forall G S ty b sL eL,
     wfEL G S eL ->
     wfSL G S ty  true  sL ->
     wfS G S ty b (StmtDo sL eL) 
 | WfSBreak : forall G S ty,
     wfS G S ty  true   StmtBreak 
 | WfSContinue : forall G S ty,
     wfS G S ty  true   StmtContinue 
 | WfSReturnVoid : forall ty_list G S ty b,
     isVoid ty ->
     wfS G S (Function ty ty_list) b  StmtReturnVoid 
 | WfSReturn : forall ty_list G S ty b eL,
      ~ isVoid ty ->
     wfEL G S eL ->
     wfS G S (Function ty ty_list) b (StmtReturn eL) 
 | WfSDeclaration : forall (definition_list:list definition) G S ty b,
     (forall definition, In definition definition_list -> wfDefinition G S definition) ->
     wfS G S ty b (StmtDeclaration definition_list) 
with wfSL : gamma -> sigma -> type -> bool -> statementL -> Prop :=    (* defn wfSL *)
 | WfSLDef : forall G S ty b l s,
     wfS G S ty b s ->
     wfSL G S ty b (StmtLDef l s) 
with wfDefinition : gamma -> sigma -> definition -> Prop :=    (* defn wfDefinition *)
 | WfDefinitionDef : forall G S v eL ty,
     (GammaMap.find v G = Some ty) ->
     wfEL G S eL ->
     wfDefinition G S (DefinitionDef v eL)
with wfGamma : gamma -> Prop :=   (* defn wfGamma *)
 | WfGammaDef : forall G,
     (forall v ty, GammaMap.find v G = Some ty ->
        wfGamma G /\ wfTy ty /\ ~ isFunction ty /\ isComplete ty) ->
     wfGamma G
with wfSigma : sigma -> sigma -> Prop :=    (* defn wfSigma *)
 | WfSigmaDef : forall S S',
     (forall v ty sL, GammaMap.find v S' = Some (ty,  sL)  ->
        wfTy ty /\ isFunction ty /\ wfSL (GammaMap.empty _) S ty false sL) ->
     wfSigma S S'
with wfProgram : program -> Prop :=    (* defn wfProgram *)
 | WfProgramDef : forall v S ty (sL:statementL),
     wfSigma S S ->
     SigmaMap.find v S = Some (ty, sL)  ->
     wfProgram (Program v S).
