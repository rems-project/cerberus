Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import Metatheory.

Module LLVMinterpreter.

Export LLVMsyntax.
Export LLVMlib.

Inductive GenericValue : Set := 
| GenericValue_int : forall (n:nat), GenericValue
| GenericValue_untyped : forall (n:nat), GenericValue
.

Definition Mem := id -> option GenericValue.

Definition updateMem (m:Mem) (i:id) (v:GenericValue) : Mem :=
fun i' =>
  if (eq_dec i i')
  then Some v
  else m i'
.

Record ExecutionContext : Set := mkExecutionContext {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;
Terminator  : terminator;
Values      : Mem;
VarArgs     : list GenericValue;
Caller      : insn
}.

Definition ECStack := list ExecutionContext.

Record State : Set := mkState {
CurSystem   : system;
CurModule   : module;
ExistValue  : option GenericValue;
ECS         : ECStack
}.

Inductive wfExecutionContext : ExecutionContext -> Prop :=
| wfExecutionContext_intro : forall EC fh lb l lp lc tmn,
  EC.(CurFunction) = fdef_intro fh lb ->
  In EC.(CurBB) lb ->
  EC.(CurBB) = block_intro l lp lc tmn ->
  (exists done, done ++ EC.(CurCmds) = lc) ->
  wfExecutionContext EC
.

Inductive wfECStack : ECStack -> Prop :=
| wfECStack_nil : wfECStack nil
| wfECStack_cons : forall EC ECS,
  wfExecutionContext EC ->
  wfECStack ECS ->
  wfECStack (EC::ECS)
.

Inductive wfContexts : State -> Prop :=
| wfContexts_intro : forall ECS ExistValue s m,
  wfECStack ECS ->
  wfContexts (mkState s m ExistValue ECS)
.

Definition getCallerReturnID (Caller:cmd) : option id :=
match Caller with
(* | insn_invoke i _ _ _ _ _ => Some i *)
| insn_call id false _ _ _ _ => Some id
| insn_call id true _ _ _ _ => None
| _ => None
end.

Fixpoint getIdViaLabelFromIdls (idls:list_value_l) (l0:l) : option id :=
match idls with
| Nil_list_value_l => None
| Cons_list_value_l (value_id id1) l1 idls'=>
  if (eq_dec l1 l0)
  then Some id1
  else getIdViaLabelFromIdls idls' l0
| Cons_list_value_l _ l1 idls'=>
  getIdViaLabelFromIdls idls' l0
end.

Definition getIdViaBlockFromIdls (idls:list_value_l) (b:block) : option id :=
match b with
| block_intro l _ _ _ => getIdViaLabelFromIdls idls l
end.

Definition getIdViaBlockFromPHINode (i:phinode) (b:block) : option id :=
match i with
| insn_phi _ _ idls => getIdViaBlockFromIdls idls b
end.

Definition getPHINodesFromBlock (b:block) : phinodes :=
match b with
| (block_intro _ ps _ _) => ps
end.

Fixpoint getIncomingValuesForBlockFromPHINodes (PNs:phinodes) (b:block) (Values:Mem) : list (id*(option GenericValue)) :=
match PNs with
| nil => nil
| PN::PNs => 
  match (getIdViaBlockFromPHINode PN b) with
  | None => getIncomingValuesForBlockFromPHINodes PNs b Values
  | Some id => (id, Values id)::getIncomingValuesForBlockFromPHINodes PNs b Values
  end
end.

Fixpoint updateValusForNewBlock (ResultValues:list (id*(option GenericValue))) (Values:Mem) : Mem :=
match ResultValues with
| nil => Values
| (id, Some v)::ResultValues' => updateMem (updateValusForNewBlock ResultValues' Values) id v
| _::ResultValues' => updateValusForNewBlock ResultValues' Values
end.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryInsn (b:block) : list cmd :=
match b with
| block_intro _ _ li _ => li
end.

(*
  SwitchToNewBasicBlock - This method is used to jump to a new basic block.
  This function handles the actual updating of block and instruction iterators
  as well as execution of all of the PHI nodes in the destination block.
 
  This method does this because all of the PHI nodes must be executed
  atomically, reading their inputs before any of the results are updated.  Not
  doing this can cause problems if the PHI nodes depend on other PHI nodes for
  their inputs.  If the input PHI node is updated before it is read, incorrect
  results can happen.  Thus we use a two phase approach.
*)
Definition switchToNewBasicBlock (Dest:block) (PrevBB:block) (Values:Mem): (block*Mem) :=
  let PNs := getPHINodesFromBlock Dest in
  let ResultValues := getIncomingValuesForBlockFromPHINodes PNs Dest Values in
  (Dest, updateValusForNewBlock ResultValues Values).

(* FIXME: Interpreter::getOperandValue is more complicated than this definition...
*)
Definition getOperandValue (v:value) (Values:Mem) : option GenericValue := 
match v with
| value_id id => Values id
| value_const (const_int _ n) => Some (GenericValue_int 0)
| value_const (const_undef _) => Some (GenericValue_int 0)
| _ => None
end.

Fixpoint params2OpGenericValues (lp:params) (Values:Mem) : list (option GenericValue):=
match lp with
| nil => nil
| (_, v)::lp' => getOperandValue v Values::params2OpGenericValues lp' Values
end.

Fixpoint _initializeFrameValues (la:args) (lg:list GenericValue) (Values:Mem) : Mem :=
match (la, lg) with
| ((_, id)::la', g::lg') => updateMem (_initializeFrameValues la' lg' Values) id g
| _ => Values
end.

Definition initializeFrameValues (la:args) (lg:list GenericValue): Mem := 
_initializeFrameValues la lg (fun _ => None).

Fixpoint opGenericValues2GenericValues (lg:list (option GenericValue)) : list GenericValue :=
match lg with
| nil => nil
| (Some g)::lg' => g::opGenericValues2GenericValues lg'
| _::lg' => opGenericValues2GenericValues lg'
end.

Record Event : Set := mkEvent { }.

Inductive trace : Set :=
| trace_nil : trace
| trace_cons : Event -> trace -> trace
.

CoInductive Trace : Set :=
| Trace_cons : Event -> Trace -> Trace
.

Fixpoint trace_app (t1 t2:trace) : trace :=
match t1 with
| trace_nil => t2
| trace_cons t t1' => trace_cons t (trace_app t1' t2)
end.

Fixpoint Trace_app (t1:trace) (t2:Trace) : Trace :=
match t1 with
| trace_nil => t2
| trace_cons t t1' => Trace_cons t (Trace_app t1' t2)
end.

Inductive visitInst : State -> State -> trace -> Prop := .

Inductive op_converges : State -> State -> trace -> Prop :=
| op_converges_nil : forall S, op_converges S S trace_nil
| op_converges_cons : forall S1 S2 S3 t1 t2,
    visitInst S1 S2 t1 ->
    op_converges S2 S3 t2 ->
    op_converges S1 S3 (trace_app t1 t2)
.

CoInductive op_diverges : State -> State -> Trace -> Prop :=
| op_diverges_intro : forall S1 S2 S3 t1 t2,
    visitInst S1 S2 t1 ->
    op_diverges S2 S3 t2 ->
    op_diverges S1 S3 (Trace_app t1 t2)
.

Definition genInitState (s:system) (main:id) (VarArgs:list GenericValue) :=
match (lookupFdefViaIDFromSystem s main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction s) with
  | None => None
  | Some CurModule =>
    match (getEntryBlock CurFunction) with
    | None => None
    | Some (block_intro l ps cs tmn) => 
        match CurFunction with 
        | fdef_intro (fheader_intro rt _ la) _ =>
          let Values := initializeFrameValues la VarArgs in
          Some
            (mkState
              s
              CurModule
              None
              ((mkExecutionContext 
                CurFunction 
                (block_intro l ps cs tmn) 
                cs
                tmn
                Values 
                VarArgs 
                (insn_cmd (insn_call main false false rt (value_id main) nil))
              )::nil)
           )          
        end
    end
  end
end.

Definition isFinialState (S:State) : bool :=
match S with
| (mkState _ _ _ nil) => true
| _ => false
end.

Inductive converges : system -> id -> list GenericValue -> State -> Prop :=
| converges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) t,
  genInitState s main VarArgs = Some IS ->
  op_converges IS FS t ->
  isFinialState FS ->
  converges s main VarArgs FS
.

Inductive diverges : system -> id -> list GenericValue -> Prop :=
| diverges_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS S:State) t,
  genInitState s main VarArgs = Some IS ->
  op_diverges IS S t ->
  diverges s main VarArgs
.

Inductive goeswrong : system -> id -> list GenericValue -> State -> Prop :=
| goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GenericValue) (IS FS:State) t,
  genInitState s main VarArgs = Some IS ->
  op_converges IS FS t ->
  ~ isFinialState FS ->
  goeswrong s main VarArgs FS
.

End LLVMinterpreter.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../monads" "-I" "../ott" "-I" "../") ***
*** End: ***
 *)
