Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "./GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import Ensembles.
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
Require Import targetdata.
Require Import infrastructure_props.
Require Import typings.
Require Import typings_props.

(************** GVs Interface ******************)

Import LLVMsyntax.
Import LLVMtd.
Import LLVMinfra.
Import LLVMgv.
Import LLVMtypings.

Structure GenericValues := mkGVs {
GVsT : Type;
instantiate_gvs : GenericValue -> GVsT -> Prop;

inhabited : GVsT -> Prop;

cgv2gvs : GenericValue -> typ -> GVsT;

gv2gvs : GenericValue -> typ -> GVsT;

lift_op1 : (GenericValue -> option GenericValue) -> GVsT -> typ -> option GVsT;

lift_op2 : (GenericValue -> GenericValue -> option GenericValue) -> 
  GVsT -> GVsT -> typ -> option GVsT;

cgv2gvs__getTypeSizeInBits : forall S los nts gv t sz al gv',
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  instantiate_gvs gv' (cgv2gvs gv t) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = 
    sizeGenericValue gv';

cgv2gvs__inhabited : forall gv t, inhabited (cgv2gvs gv t);

gv2gvs__getTypeSizeInBits : forall S los nts gv t sz al,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) = sizeGenericValue gv ->
  forall gv', instantiate_gvs gv' (gv2gvs gv t) ->
  sizeGenericValue gv' = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8);

gv2gvs__inhabited : forall gv t, inhabited (gv2gvs gv t);

lift_op1__inhabited : forall f gvs1 t gvs2
  (H:forall x, exists z, f x = Some z),
  inhabited gvs1 -> 
  lift_op1 f gvs1 t = Some gvs2 ->
  inhabited gvs2;

lift_op2__inhabited : forall f gvs1 gvs2 t gvs3
  (H:forall x y, exists z, f x y = Some z),
  inhabited gvs1 -> inhabited gvs2 -> 
  lift_op2 f gvs1 gvs2 t = Some gvs3 ->
  inhabited gvs3;

lift_op1__isnt_stuck : forall f gvs1 t
  (H:forall x, exists z, f x = Some z),
  exists gvs2, lift_op1 f gvs1 t = Some gvs2;

lift_op2__isnt_stuck : forall f gvs1 gvs2 t
  (H:forall x y, exists z, f x y = Some z),
  exists gvs3, lift_op2 f gvs1 gvs2 t = Some gvs3;

lift_op1__getTypeSizeInBits : forall S los nts f g t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y, instantiate_gvs x g -> f x = Some y -> 
   sizeGenericValue y = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op1 f g t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8);

lift_op2__getTypeSizeInBits : forall S los nts f g1 g2 t sz al gvs,
  wf_typ S t ->
  _getTypeSizeInBits_and_Alignment los 
    (getTypeSizeInBits_and_Alignment_for_namedts (los,nts) true) true t = 
      Some (sz, al) ->
  (forall x y z, 
   instantiate_gvs x g1 -> instantiate_gvs y g2 -> f x y = Some z -> 
   sizeGenericValue z = nat_of_Z (ZRdiv (Z_of_nat sz) 8)) ->
  lift_op2 f g1 g2 t = Some gvs ->
  forall gv : GenericValue,
  instantiate_gvs gv gvs ->
  sizeGenericValue gv = nat_of_Z (ZRdiv (Z_of_nat sz) 8);

inhabited_inv : forall gvs, inhabited gvs -> exists gv, instantiate_gvs gv gvs;

instantiate_gv__gv2gvs : forall gv t, instantiate_gvs gv (gv2gvs gv t);

none_undef2gvs_inv : forall gv gv' t,
  instantiate_gvs gv (gv2gvs gv' t) -> (forall mc, (Vundef, mc)::nil <> gv') -> 
  gv = gv'
}.

Global Opaque GVsT gv2gvs instantiate_gvs inhabited cgv2gvs gv2gvs lift_op1 lift_op2.

(************** Opsem ***************************************************** ***)

Module OpsemAux.

(**************************************)
(* To realize it in LLVM, we can try to dynamically cast fptr to Function*, 
   if failed, return None
   if successeful, we can return this function's name *)
Fixpoint lookupFdefViaGVFromFunTable (fs:GVMap)(fptr:GenericValue): option id :=
match fs with
| nil => None
| (id0,gv0)::fs' => 
  if eq_gv gv0 fptr
  then Some id0 
  else lookupFdefViaGVFromFunTable fs' fptr
end.

Definition lookupFdefViaPtr Ps fs fptr : option fdef :=
  do fn <- lookupFdefViaGVFromFunTable fs fptr;
     lookupFdefViaIDFromProducts Ps fn.

Definition lookupExFdecViaPtr (Ps:products) (fs:GVMap) fptr : option fdec :=
do fn <- lookupFdefViaGVFromFunTable fs fptr;
    match lookupFdefViaIDFromProducts Ps fn with 
    | Some _ => None
    | None => lookupFdecViaIDFromProducts Ps fn
    end
.

Axiom callExternalFunction : mem -> id -> list GenericValue -> 
  option ((option GenericValue)*mem).

Definition initGlobal (TD:TargetData)(gl:GVMap)(Mem:mem)(id0:id)(t:typ)(c:const)
  (align0:align) : option (GenericValue*mem) :=
  do tsz <- getTypeAllocSize TD t;
  do gv <- LLVMgv.const2GV TD gl c;
     match (malloc_one TD Mem (Size.from_nat tsz) align0) with
     | Some (Mem', mb) =>
       do Mem'' <- mstore TD Mem' (blk2GV TD mb) t gv align0;
       ret (blk2GV TD mb,  Mem'')
     | None => None
     end.

Definition initTargetData (los:layouts)(nts:namedts)(Mem:mem) : TargetData := 
  (los, nts).

Axiom getExternalGlobal : mem -> id -> option GenericValue.

(* For each function id, the runtime emits an address as a function pointer. 
   It can be realized by taking Function* in LLVM as the address. *)
Axiom initFunTable : mem -> id -> option GenericValue.

Fixpoint genGlobalAndInitMem (TD:TargetData)(Ps:list product)(gl:GVMap)(fs:GVMap)
  (Mem:mem) : option (GVMap*GVMap*mem) :=
match Ps with
| nil => Some (gl, fs, Mem)
| (product_gvar (gvar_intro id0 _ spec t c align))::Ps' => 
  match (initGlobal TD gl Mem id0 t c align) with
  | Some (gv, Mem') => 
      genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem'
  | None => None
  end
| (product_gvar (gvar_external id0 spec t))::Ps' => 
  match (getExternalGlobal Mem id0) with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) fs Mem
  | None => None
  end
| (product_fdef (fdef_intro (fheader_intro _ _ id0 _ _) _))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) 
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
| (product_fdec (fdec_intro (fheader_intro _ _ id0 _ _)))::Ps' =>
  match initFunTable Mem id0 with
  | Some gv => genGlobalAndInitMem TD Ps' (updateAddAL _ gl id0 gv) 
      (updateAddAL _ fs id0 gv) Mem
  | None => None
  end
end.

Lemma lookupFdefViaPtr_inversion : forall Ps fs fptr f,
  lookupFdefViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupFdefViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0. eauto.
Qed.  

Lemma lookupExFdecViaPtr_inversion : forall Ps fs fptr f,
  lookupExFdecViaPtr Ps fs fptr = Some f ->
  exists fn,
    lookupFdefViaGVFromFunTable fs fptr = Some fn /\
    lookupFdefViaIDFromProducts Ps fn = None /\
    lookupFdecViaIDFromProducts Ps fn = Some f.
Proof.
  intros.
  unfold lookupExFdecViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fptr); tinv H.
  simpl in H. exists i0. 
  destruct (lookupFdefViaIDFromProducts Ps i0); inv H; auto.
Qed.  

Lemma lookupFdefViaPtr_inv : forall Ps fs fv F,
  lookupFdefViaPtr Ps fs fv = Some F ->
  InProductsB (product_fdef F) Ps.
Proof.
  intros.
  unfold lookupFdefViaPtr in H.
  destruct (lookupFdefViaGVFromFunTable fs fv); try solve [inversion H].
  apply lookupFdefViaIDFromProducts_inv in H; auto.
Qed.

Lemma lookupFdefViaPtr_uniq : forall los nts Ps fs S fptr F,
  uniqSystem S ->
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fptr = Some F ->
  uniqFdef F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H1.
  destruct H1 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2; auto.
  apply uniqSystem__uniqProducts in H0; auto.
  eapply uniqProducts__uniqFdef; simpl; eauto.
Qed.

Lemma entryBlockInSystemBlockFdef'' : forall los nts Ps fs fv F S B,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  getEntryBlock F = Some B ->
  blockInSystemModuleFdef B S (module_intro los nts Ps) F.
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply entryBlockInFdef in H1.  
  apply blockInSystemModuleFdef_intro; auto.
Qed.

Lemma lookupFdefViaPtrInSystem : forall los nts Ps fs S fv F,
  moduleInSystem (module_intro los nts Ps) S ->
  lookupFdefViaPtr Ps fs fv = Some F ->
  productInSystemModuleB (product_fdef F) S (module_intro los nts Ps).
Proof.
  intros.
  apply lookupFdefViaPtr_inversion in H0.
  destruct H0 as [fn [J1 J2]].
  apply lookupFdefViaIDFromProducts_inv in J2.
  apply productInSystemModuleB_intro; auto.
Qed.

Record Config : Type := mkCfg {
CurSystem          : system;
CurTargetData      : TargetData;
CurProducts        : list product;
Globals            : GVMap;
FunTable           : GVMap
}.

Record bConfig : Type := mkbCfg {
bCurSystem          : system;
bCurTargetData      : TargetData;
bCurProducts        : list product;
bGlobals            : GVMap;
bFunTable           : GVMap;
bCurFunction        : fdef
}.

End OpsemAux.

Module Opsem. 

Export LLVMsyntax.
Export LLVMtd.
Export LLVMinfra.
Export LLVMgv.
Export LLVMtypings.
Export OpsemAux.

Section Opsem. 

Context `{GVsSig : GenericValues}.

Notation GVs := GVsSig.(GVsT).
Definition GVsMap := list (id * GVs).
Notation "gv @ gvs" := 
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).

Definition in_list_gvs (l1 : list GenericValue) (l2 : list GVs) : Prop :=
List.Forall2 GVsSig.(instantiate_gvs) l1 l2.

Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss) 
  (at level 43, right associativity).

Definition const2GV (TD:TargetData) (gl:GVMap) (c:const) : option GVs :=
match (_const2GV TD gl c) with
| None => None
| Some (gv, ty) => Some (GVsSig.(cgv2gvs) gv ty)
end.

Definition getOperandValue (TD:TargetData) (v:value) (locals:GVsMap) 
  (globals:GVMap) : option GVs := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => const2GV TD globals c
end.

(**************************************)
(** Execution contexts *)

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVsMap;                (* LLVM values used in this invocation *)
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

(* FunTable maps function names to their addresses that are taken as function 
   pointers. When we are calling a function via an id, we first search in Globals
   via the value id to get its address, and then search in FunTable to get its
   name, via the name, we search in CurProducts to get its definition.

   We assume that there is an 'initFunTable' that returns function addresses to
   initialize FunTable
*)
Record State : Type := mkState {
ECS                : ECStack;
Mem                : mem
}.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (globals:GVMap) (locals:GVsMap) : 
  option (list (id*GVs)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue TD v locals globals, 
             getIncomingValuesForBlockFromPHINodes TD PNs b globals locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end               
  end
end.

Fixpoint updateValuesForNewBlock (ResultValues:list (id*GVs)) (locals:GVsMap) 
  : GVsMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' => 
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) 
  (PrevBB:block) (globals: GVMap) (locals:GVsMap): option GVsMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB globals locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

Fixpoint params2GVs (TD:TargetData) (lp:params) (locals:GVsMap) (globals:GVMap) :
 option (list GVs) :=
match lp with
| nil => Some nil
| (_, v)::lp' => 
    match (getOperandValue TD v locals globals, 
           params2GVs TD lp' locals globals) with
    | (Some gv, Some gvs) => Some (gv::gvs)
    | _ => None
    end
end.

(**************************************)
(* Realized by libffi in LLVM *)
Definition exCallUpdateLocals TD (ft:typ) (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVsMap) : option GVsMap :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => 
          match ft with
          | typ_function t _ _ => 
            match fit_gv TD t Result with
            | Some gr => Some (updateAddAL _ lc rid ($ gr # t $))
            | _ => None
            end
          | _ => None
          end
      end
  | true => Some lc
  end.

Fixpoint values2GVs (TD:TargetData) (lv:list_sz_value) (locals:GVsMap) 
  (globals:GVMap) : option (list GVs):=
match lv with
| Nil_list_sz_value => Some nil
| Cons_list_sz_value _ v lv' => 
  match (getOperandValue TD v locals globals) with
  | Some GV => 
    match (values2GVs TD lv' locals globals) with
    | Some GVs => Some (GV::GVs)
    | None => None
    end
  | None => None
  end
end.

Fixpoint _initializeFrameValues TD (la:args) (lg:list GVs) (locals:GVsMap) 
  : option GVsMap :=
match (la, lg) with
| (((t, _), id)::la', g::lg') => 
  match _initializeFrameValues TD la' lg' locals,
        GVsSig.(lift_op1) (fit_gv TD t) g t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id gv)
  | _, _ => None
  end
| (((t, _), id)::la', nil) => 
  (* FIXME: We should initalize them w.r.t their type size. *)
  match _initializeFrameValues TD la' nil locals, gundef TD t with
  | Some lc', Some gv => Some (updateAddAL _ lc' id ($ gv # t $))
  | _, _ => None
  end
| _ => Some locals
end.

Definition initLocals TD (la:args) (lg:list GVs): option GVsMap := 
_initializeFrameValues TD la lg nil.

Definition BOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:bop) (bsz:sz) 
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    GVsSig.(lift_op2) (mbop TD op bsz) gvs1 gvs2 (typ_int bsz)
| _ => None
end
.

Definition FBOP (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:fbop) fp
  (v1 v2:value) : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    GVsSig.(lift_op2) (mfbop TD op fp) gvs1 gvs2 (typ_floatpoint fp)
| _ => None
end
.

Definition ICMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c t (v1 v2:value) 
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    GVsSig.(lift_op2) (micmp TD c t) gvs1 gvs2 (typ_int Size.One)
| _ => None
end
.

Definition FCMP (TD:TargetData) (lc:GVsMap) (gl:GVMap) c fp (v1 v2:value) 
  : option GVs :=
match (getOperandValue TD v1 lc gl, getOperandValue TD v2 lc gl) with
| (Some gvs1, Some gvs2) => 
    GVsSig.(lift_op2) (mfcmp TD c fp) gvs1 gvs2 (typ_int Size.One)
| _ => None
end
.

Definition CAST (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:castop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mcast TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition TRUNC (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:truncop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mtrunc TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition EXT (TD:TargetData) (lc:GVsMap) (gl:GVMap) (op:extop) 
  (t1:typ) (v1:value) (t2:typ) : option GVs:=
match (getOperandValue TD v1 lc gl) with
| (Some gvs1) => GVsSig.(lift_op1) (mext TD op t1 t2) gvs1 t2
| _ => None
end
.

Definition GEP (TD:TargetData) (ty:typ) (mas:GVs) (vidxs:list GenericValue) 
  (inbounds:bool) : option GVs :=
GVsSig.(lift_op1) (gep TD ty vidxs inbounds) mas 
  (typ_pointer (typ_int Size.One)).

Definition extractGenericValue (TD:TargetData) (t:typ) (gvs : GVs) 
  (cidxs : list_const) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, t') => GVsSig.(lift_op1) (mget' TD o t') gvs t'
  | None => None
  end
end.

Definition insertGenericValue (TD:TargetData) (t:typ) (gvs:GVs)
  (cidxs:list_const) (t0:typ) (gvs0:GVs) : option GVs :=
match (intConsts2Nats TD cidxs) with
| None => None
| Some idxs =>
  match (mgetoffset TD t idxs) with
  | Some (o, _) => GVsSig.(lift_op2) (mset' TD o t t0) gvs gvs0 t
  | None => None
  end
end.

(***************************************************************)
(* deterministic small-step *)

Definition returnUpdateLocals (TD:TargetData) (c':cmd) (Result:value) 
  (lc lc':GVsMap) (gl:GVMap) : option GVsMap :=
  match (getOperandValue TD Result lc gl) with
  | Some gr =>    
      match c' with
      | insn_call id0 false _ t _ _ => 
        match t with
        | typ_function ct _ _ =>
           match (GVsSig.(lift_op1) (fit_gv TD ct) gr ct) with
           | Some gr' => Some (updateAddAL _ lc' id0 gr')
           | _ => None
           end
        | _ => None
        end
      | insn_call _ _ _ _ _ _ => Some lc'
      | _=> None
      end
  | None => None
  end.

Inductive sInsn : Config -> State -> State -> trace -> Prop :=
| sReturn : forall S TD Ps F B rid RetTy Result lc gl fs
                            F' B' c' cs' tmn' lc' EC
                            Mem Mem' als als' lc'',   
  Instruction.isCallInst c' = true ->
  (* FIXME: we should get Result before free?! *)
  free_allocas TD Mem als = Some Mem' ->
  returnUpdateLocals TD c' Result lc lc' gl = Some lc'' ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState ((mkEC F B nil (insn_return rid RetTy Result) lc als)::
              (mkEC F' B' (c'::cs') tmn' lc' als')::EC) Mem)
    (mkState ((mkEC F' B' cs' tmn' lc'' als')::EC) Mem')
    trace_nil

| sReturnVoid : forall S TD Ps F B rid lc gl fs
                            F' B' c' tmn' lc' EC
                            cs' Mem Mem' als als',   
  Instruction.isCallInst c' = true ->
  free_allocas TD Mem als = Some Mem' ->
  getCallerReturnID c' = None ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState ((mkEC F B nil (insn_return_void rid) lc als)::
              (mkEC F' B' (c'::cs') tmn' lc' als')::EC) Mem)
    (mkState ((mkEC F' B' cs' tmn' lc' als')::EC) Mem')
    trace_nil 

| sBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              l' ps' cs' tmn' lc' EC Mem als,   
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState ((mkEC F B nil (insn_br bid Cond l1 l2) lc als)::EC) Mem)
    (mkState ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)::EC) Mem)
    trace_nil 

| sBranch_uncond : forall S TD Ps F B lc gl fs bid l 
                           l' ps' cs' tmn' lc' EC Mem als,   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState ((mkEC F B nil (insn_br_uncond bid l) lc als)::EC) Mem)
    (mkState ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' als)::EC) Mem)
    trace_nil 

| sBop: forall S TD Ps F B lc gl fs id bop sz v1 v2 gvs3 EC cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)
    (mkState ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) Mem)
    trace_nil 

| sFBop: forall S TD Ps F B lc gl fs id fbop fp v1 v2 gvs3 EC cs tmn Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc als)::EC) Mem)
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) Mem)
    trace_nil 

| sExtractValue : forall S TD Ps F B lc gl fs id t v gvs gvs' idxs EC cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gvs ->
  extractGenericValue TD t gvs idxs = Some gvs' ->
  sInsn (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc als)::EC) 
               Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs') als)::EC) Mem)
    trace_nil

| sInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gvs gvs' gvs'' idxs 
                         EC cs tmn Mem als,
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD v' lc gl = Some gvs' ->
  insertGenericValue TD t gvs idxs t' gvs' = Some gvs'' ->
  sInsn (mkCfg S TD Ps gl fs) 
    (mkState ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn 
                    lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs'') als)::EC) Mem)
    trace_nil 

| sMalloc : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc als) ::EC) Mem) 
    (mkState ((mkEC F B cs tmn 
                (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $)) 
                als)::EC) Mem')
    trace_nil

| sFree : forall S TD Ps F B lc gl fs fid t v EC cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_free fid t v)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn lc als)::EC) Mem')
    trace_nil

| sAlloca : forall S TD Ps F B lc gl fs id t v gns gn align EC cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn 
                   (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $)) 
                   (mb::als))::EC) Mem')
    trace_nil

| sLoad : forall S TD Ps F B lc gl fs id t align v EC cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_load id t v align)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id ($ gv # t $)) als)::EC) Mem)
    trace_nil

| sStore : forall S TD Ps F B lc gl fs sid t align v1 v2 EC cs tmn Mem als 
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_store sid t v1 v2 align)::cs) tmn lc als)::EC) 
               Mem) 
    (mkState ((mkEC F B cs tmn lc als)::EC) Mem')
    trace_nil

| sGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs vidxss EC mp mp' 
                 cs tmn Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxss ->
  vidxs @@ vidxss ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_gep id inbounds t v idxs)::cs) tmn lc als)::EC) 
               Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id mp') als)::EC) Mem)
    trace_nil 

| sTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gvs2 EC cs tmn 
                   Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als)::EC)
               Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) Mem)
    trace_nil

| sExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gvs2 EC cs tmn Mem 
                 als,
  EXT TD lc gl extop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) Mem)
    trace_nil

| sCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gvs2 EC cs tmn Mem 
                  als,
  CAST TD lc gl castop t1 v1 t2 = Some gvs2 ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc als)::EC) 
               Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs2) als)::EC) Mem)
    trace_nil

| sIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gvs3 EC cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) Mem)
    trace_nil

| sFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gvs3 EC cs tmn Mem 
                  als,
  FCMP TD lc gl fcond fp v1 v2 = Some gvs3 ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc als)::EC) Mem)
    (mkState ((mkEC F B cs tmn (updateAddAL _ lc id gvs3) als)::EC) Mem)
    trace_nil

| sSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 cond c EC cs tmn Mem als 
                    gvs1 gvs2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some gvs2 ->
  c @ cond ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc als)::EC) Mem) 
    (mkState ((mkEC F B cs tmn (if isGVZero TD c 
                                then updateAddAL _ lc id gvs2 
                                else updateAddAL _ lc id gvs1) als)::EC) Mem)
    trace_nil

| sCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn fptrs fptr
                      lc' l' ps' cs' tmn' EC rt la va lb Mem als ft fa gvs,
  (* only look up the current module for the time being, 
     do not support linkage. *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc' ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) Mem)
    (mkState ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                       (block_intro l' ps' cs' tmn') cs' tmn' lc' nil)::
              (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) Mem)
    trace_nil 

| sExCall : forall S TD Ps F B lc gl fs rid noret ca fid fv lp cs tmn EC 
                    rt la Mem als oresult Mem' lc' va ft fa gvs fptr fptrs gvss,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  sInsn (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn 
                       lc als)::EC) Mem)
    (mkState ((mkEC F B cs tmn lc' als)::EC) Mem')
    trace_nil 
.

Definition s_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem) 
  : option (Config * State) :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurLayouts CurNamedts CurProducts) =>
    let initargetdata := 
      initTargetData CurLayouts CurNamedts initmem in 
    match (genGlobalAndInitMem initargetdata CurProducts nil nil 
      initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (block_intro l ps cs tmn) => 
          match CurFunction with 
          | fdef_intro (fheader_intro _ rt _ la _) _ =>
            match initLocals initargetdata la Args with
            | Some Values =>
              Some
              (mkCfg
                S
                initargetdata
                CurProducts
                initGlobal
                initFunTable,
               mkState
                ((mkEC
                  CurFunction 
                  (block_intro l ps cs tmn) 
                  cs
                  tmn
                  Values 
                  nil
                )::nil)
                initMem
              )          
            | None => None
            end
        end
      end
    end
  end
end.

Definition s_isFinialState (state:State) : bool :=
match state with
| (mkState ((mkEC _ _ nil (insn_return_void _) _ _)::nil) _ ) => true
| (mkState ((mkEC _ _ nil (insn_return _ _ _) _ _)::nil) _ ) => true 
| _ => false
end.

Inductive sop_star (cfg:Config) : State -> State -> trace -> Prop :=
| sop_star_nil : forall state, sop_star cfg state state trace_nil
| sop_star_cons : forall state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_star cfg state1 state3 (trace_app tr1 tr2)
.

Inductive sop_plus (cfg:Config) : State -> State -> trace -> Prop :=
| sop_plus_cons : forall state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_plus cfg state1 state3 (trace_app tr1 tr2)
.

CoInductive sop_diverges (cfg:Config) : State -> Trace -> Prop :=
| sop_diverges_intro : forall state1 state2 tr1 tr2,
    sop_plus cfg state1 state2 tr1 ->
    sop_diverges cfg state2 tr2 ->
    sop_diverges cfg state1 (Trace_app tr1 tr2)
.

Inductive s_converges : system -> id -> list GVs -> State -> Prop :=
| s_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              cfg (IS FS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_star cfg IS FS tr ->
  s_isFinialState FS ->
  s_converges s main VarArgs FS
.

Inductive s_diverges : system -> id -> list GVs -> Trace -> Prop :=
| s_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                             cfg (IS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_diverges cfg IS tr ->
  s_diverges s main VarArgs tr
.

Inductive s_goeswrong : system -> id -> list GVs -> State -> Prop :=
| s_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              cfg (IS FS:State) tr,
  s_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  sop_star cfg IS FS tr ->
  ~ s_isFinialState FS ->
  s_goeswrong s main VarArgs FS
.

(***************************************************************)
(* deterministic big-step *)

Definition callUpdateLocals (TD:TargetData) ft (noret:bool) (rid:id) 
  (oResult:option value) (lc lc':GVsMap) (gl:GVMap) : option GVsMap :=
    match noret with
    | false =>
        match oResult with
        | None => None
        | Some Result => 
          match getOperandValue TD Result lc' gl with 
          | Some gr =>  
            match ft with
            | typ_function t _ _ => 
              match (GVsSig.(lift_op1) (fit_gv TD t) gr t) with
              | Some gr' => Some (updateAddAL _ lc rid gr')
              | None => None
              end
            | _ => None
            end
          | None => None
          end
        end
    | true => 
        match oResult with
        | None => Some lc
        | Some Result => 
          match (getOperandValue TD Result lc' gl) with 
          | Some gr => Some lc
          | None => None
          end
        end
    end.

Record bExecutionContext : Type := mkbEC {
bCurBB       : block;
bCurCmds     : cmds;                  (* cmds to run within CurBB *)
bTerminator  : terminator;
bLocals      : GVsMap;                (* LLVM values used in this invocation *)
bAllocas     : list mblock;           (* Track memory allocated by alloca *)
bMem         : mem
}.

Inductive bInsn : 
    bConfig -> bExecutionContext -> bExecutionContext -> trace ->  Prop :=
| bBranch : forall S TD Ps F B lc gl fs bid Cond l1 l2 conds c
                              l' ps' cs' tmn' Mem als lc',   
  getOperandValue TD Cond lc gl = Some conds ->
  c @ conds ->
  Some (block_intro l' ps' cs' tmn') = (if isGVZero TD c
               then lookupBlockViaLabelFromFdef F l2
               else lookupBlockViaLabelFromFdef F l1) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B nil (insn_br bid Cond l1 l2) lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als Mem)
    trace_nil

| bBranch_uncond : forall S TD Ps F B lc gl fs l bid
                              l' ps' cs' tmn' Mem als lc',   
  Some (block_intro l' ps' cs' tmn') = (lookupBlockViaLabelFromFdef F l) ->
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc = Some lc'->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B nil (insn_br_uncond bid l) lc als Mem)
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc' als Mem)
    trace_nil

| bBop : forall S TD Ps F B lc gl fs id bop sz v1 v2 gv3 cs tmn Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_bop id bop sz v1 v2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    trace_nil 

| bFBop : forall S TD Ps F B lc gl fs id fbop fp v1 v2 gv3 cs tmn Mem 
                  als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    trace_nil 

| bExtractValue : forall S TD Ps F B lc gl fs id t v gv gv' idxs cs tmn 
                          Mem als,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_extractvalue id t v idxs)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv') als Mem)
    trace_nil 

| bInsertValue : forall S TD Ps F B lc gl fs id t v t' v' gv gv' gv'' idxs
                         cs tmn Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  bInsn (mkbCfg S TD Ps gl fs F)  
    (mkbEC B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv'') als Mem)
    trace_nil

| bMalloc : forall S TD Ps F B lc gl fs id t v gns gn align cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_malloc id t v align)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn  (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
          als Mem')
    trace_nil

| bFree : forall S TD Ps F B lc gl fs fid t v cs tmn Mem als Mem' mptrs mptr,
  getOperandValue TD v lc gl = Some mptrs ->
  mptr @ mptrs ->
  free TD Mem mptr = Some Mem'->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_free fid t v)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn lc als Mem')
    trace_nil

| bAlloca : forall S TD Ps F B lc gl fs id t v gns gn align cs tmn Mem als 
                    Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_alloca id t v align)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id ($ (blk2GV TD mb) # (typ_pointer t) $))
                    (mb::als) Mem')
    trace_nil

| bLoad : forall S TD Ps F B lc gl fs id t v align cs tmn Mem als mps mp gv,
  getOperandValue TD v lc gl = Some mps ->
  mp @ mps ->
  mload TD Mem mp t align = Some gv ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_load id t v align)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id ($ gv # t $)) als Mem)
    trace_nil

| bStore : forall S TD Ps F B lc gl fs sid t v1 v2 align cs tmn Mem als 
                   mp2 gv1 Mem' gvs1 mps2,
  getOperandValue TD v1 lc gl = Some gvs1 ->
  getOperandValue TD v2 lc gl = Some mps2 ->
  gv1 @ gvs1 -> mp2 @ mps2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  bInsn (mkbCfg S TD Ps gl fs  F)   
    (mkbEC B ((insn_store sid t v1 v2 align)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn lc als Mem')
    trace_nil

| bGEP : forall S TD Ps F B lc gl fs id inbounds t v idxs vidxs vidxss mp mp' 
                 cs tmn Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxss ->
  vidxs @@ vidxss ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_gep id inbounds t v idxs)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id mp') als Mem)
    trace_nil 

| bTrunc : forall S TD Ps F B lc gl fs id truncop t1 v1 t2 gv2 cs tmn Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    trace_nil

| bExt : forall S TD Ps F B lc gl fs id extop t1 v1 t2 gv2 cs tmn Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_ext id extop t1 v1 t2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    trace_nil

| bCast : forall S TD Ps F B lc gl fs id castop t1 v1 t2 gv2 cs tmn Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_cast id castop t1 v1 t2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv2) als Mem)
    trace_nil

| bIcmp : forall S TD Ps F B lc gl fs id cond t v1 v2 gv3 cs tmn Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_icmp id cond t v1 v2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    trace_nil

| bFcmp : forall S TD Ps F B lc gl fs id fcond fp v1 v2 gv3 cs tmn Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc als Mem)
    (mkbEC B cs tmn (updateAddAL _ lc id gv3) als Mem)
    trace_nil

| bSelect : forall S TD Ps F B lc gl fs id v0 t v1 v2 cond c cs tmn Mem als 
                    gv1 gv2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  c @ cond ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_select id v0 t v1 v2)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn (if isGVZero TD c 
                     then updateAddAL _ lc id gv2 
                     else updateAddAL _ lc id gv1) als Mem)
    trace_nil

| bCall : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                       Rid oResult tr B' lc' Mem Mem' als' als Mem'' lc'' ft,
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr ->
  free_allocas TD Mem' als' = Some Mem'' ->
  callUpdateLocals TD ft noret rid oResult lc lc' gl = Some lc'' ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_call rid noret ca ft fv lp)::cs) tmn lc als Mem) 
    (mkbEC B cs tmn lc'' als Mem'') 
    tr

| bExCall : forall S TD Ps F B lc gl fs rid noret fv fid lp cs tmn
                 rt la va Mem als oresult Mem' lc' ft fa ca gvs fptr fptrs gvss,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  bInsn (mkbCfg S TD Ps gl fs F)   
    (mkbEC B ((insn_call rid noret ca ft fv lp)::cs) tmn lc als Mem)
    (mkbEC B cs tmn lc' als Mem')
    trace_nil

with bops: bConfig -> bExecutionContext -> bExecutionContext -> trace -> Prop :=
| bops_nil : forall cfg S, bops cfg S S trace_nil
| bops_cons : forall cfg S1 S2 S3 t1 t2,
    bInsn cfg S1 S2 t1 ->
    bops cfg S2 S3 t2 ->
    bops cfg S1 S3 (trace_app t1 t2)

with bFdef : value -> typ -> params -> system -> TargetData -> products -> 
            GVsMap -> GVMap -> GVMap -> mem -> GVsMap ->
            list mblock -> mem -> block -> id -> option value -> trace -> Prop :=
| bFdef_func : forall S TD Ps gl fs fv fid lp lc rid fa lc0 fptrs fptr
   l' ps' cs' tmn' rt la lb l'' ps'' cs'' Result lc' tr Mem Mem' als' va gvs,
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bops (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb))
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem)
    (mkbEC (block_intro l'' ps'' cs'' (insn_return rid rt Result)) nil 
                             (insn_return rid rt Result) lc' als' Mem')
    tr ->
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' 
    (block_intro l'' ps'' cs'' (insn_return rid rt Result)) rid (Some Result) tr

| bFdef_proc : forall S TD Ps gl fs fv fid lp lc rid fa lc0 fptrs fptr
       l' ps' cs' tmn' rt la lb l'' ps'' cs'' lc' tr Mem Mem' als' va gvs,
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bops (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb) )
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem)
    (mkbEC (block_intro l'' ps'' cs'' (insn_return_void rid)) nil 
                            (insn_return_void rid) lc' als' Mem')
    tr ->
  bFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' 
    (block_intro l'' ps'' cs'' (insn_return_void rid)) rid None tr
.

CoInductive bInsnInf : bConfig -> bExecutionContext -> Trace -> Prop :=
| bCallInsnInf : forall S TD Ps F B lc gl fs rid noret ca rt fv lp cs tmn
                       tr Mem als ft,
  bFdefInf fv rt lp S TD Ps lc gl fs Mem tr ->
  bInsnInf (mkbCfg S TD Ps gl fs F) 
    (mkbEC B ((insn_call rid noret ca ft fv lp)::cs) tmn lc als Mem) tr

with bopInf : bConfig -> bExecutionContext -> Trace -> Prop :=
| bopInf_insn : forall cfg state1 t1,
    bInsnInf cfg state1 t1 ->
    bopInf cfg state1 t1
| bopInf_cons : forall cfg state1 state2 t1 t2,
    bInsn cfg state1 state2 t1 ->
    bopInf cfg state2 t2 ->
    bopInf cfg state1 (Trace_app t1 t2)

with bFdefInf : value -> typ -> params -> system -> TargetData -> products -> 
    GVsMap -> GVMap  -> GVMap -> mem -> Trace -> Prop :=
| bFdefInf_intro : forall S TD Ps lc gl fs fv fid lp fa lc0
                          l' ps' cs' tmn' rt la va lb tr Mem gvs fptrs fptr,
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupFdefViaPtr Ps fs fptr = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = 
    Some (block_intro l' ps' cs' tmn') ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  bopInf (mkbCfg S TD Ps gl fs (fdef_intro (fheader_intro fa rt fid la va) lb))  
    (mkbEC (block_intro l' ps' cs' tmn') cs' tmn' lc0 nil Mem)
    tr ->
  bFdefInf fv rt lp S TD Ps lc gl fs Mem tr
.

Definition b_genInitState (S:system) (main:id) (Args:list GVs) (initmem:mem) 
  : option (bConfig * bExecutionContext) :=
match s_genInitState S main Args initmem with
| Some (mkCfg S0 TD Ps gl fs, mkState ((mkEC F B cs tmn lc als)::nil) M) =>
    Some (mkbCfg S0 TD Ps gl fs F, mkbEC B cs tmn lc als M)
| _ => None
end.

Definition b_isFinialState (ec:bExecutionContext) : bool :=
match ec with
| (mkbEC _ nil (insn_return_void _) _ _ _ ) => true
| (mkbEC _ nil (insn_return _ _ _) _ _ _ ) => true 
| _ => false
end.

Inductive b_converges : system -> id -> list GVs -> bExecutionContext -> Prop :=
| b_converges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                       cfg (IS FS:bExecutionContext) tr,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bops cfg IS FS tr ->
  b_isFinialState FS ->
  b_converges s main VarArgs FS
.

Inductive b_diverges : system -> id -> list GVs -> Trace -> Prop :=
| b_diverges_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                             cfg (IS S:bExecutionContext) tr,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bopInf cfg IS tr ->
  b_diverges s main VarArgs tr
.

Inductive b_goeswrong : system -> id -> list GVs -> bExecutionContext -> Prop :=
| b_goeswrong_intro : forall (s:system) (main:id) (VarArgs:list GVs) 
                              cfg (IS FS:bExecutionContext) tr,
  b_genInitState s main VarArgs Mem.empty = Some (cfg, IS) ->
  bops cfg IS FS tr ->
  ~ b_isFinialState FS ->
  b_goeswrong s main VarArgs FS
.

Scheme bInsn_ind2 := Induction for bInsn Sort Prop
  with bops_ind2 := Induction for bops Sort Prop
  with bFdef_ind2 := Induction for bFdef Sort Prop.

Combined Scheme b_mutind from bInsn_ind2, bops_ind2, bFdef_ind2.

End Opsem. 

Hint Unfold in_list_gvs.
Hint Constructors bInsn bops bFdef sInsn sop_star sop_diverges sop_plus.

End Opsem.

Tactic Notation "sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sReturn" | c "sReturnVoid" | c "sBranch" | c "sBranch_uncond" |
    c "sBop" | c "sFBop" | c "sExtractValue" | c "sInsertValue" |
    c "sMalloc" | c "sFree" |
    c "sAlloca" | c "sLoad" | c "sStore" | c "sGEP" |
    c "sTrunc" | c "sExt" | 
    c "sCast" | 
    c "sIcmp" | c "sFcmp" | c "sSelect" |  
    c "sCall" | c "sExCall" ].

Tactic Notation "b_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "bBranch" | c "bBranch_uncond" |
    c "bBop" | c "bFBop" | c "bExtractValue" | c "bInsertValue" |
    c "bMalloc" | c "bFree" |
    c "bAlloca" | c "bLoad" | c "bStore" | c "bGEP" |
    c "bTrunc" | c "bExt" | c "bCast" | c "bIcmp" | c "bFcmp" |  c "bSelect" | 
    c "bCall" | c "bExCall" |
    c "bops_nil" | c "bops_cons" | c "bFdef_func" | c "bFdef_proc" ].

Tactic Notation "sop_star_cases" tactic(first) tactic(c) :=
  first;
  [ c "sop_star_nil" | c "sop_star_cons" ].


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
