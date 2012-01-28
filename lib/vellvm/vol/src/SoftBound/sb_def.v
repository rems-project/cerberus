Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import vellvm.

Module SBspecAux.

Record metadata : Type := mkMD {
  md_blk : Values.block; md_bofs : int32; md_eofs : int32
}.

Definition rmetadata := list (id*metadata).

Definition bound2MD (b:mblock) (s:sz) n : metadata :=
mkMD b (Int.zero 31) (Int.repr 31 ((Size.to_Z s)*n)).

Definition i8 := typ_int Size.Eight.
Definition p8 := typ_pointer i8.

Fixpoint get_const_metadata (c:const) : option (const*const) :=
match c with
| const_gid t gid => 
    match t with
    | typ_function _ _ _ => Some (const_castop castop_bitcast c p8,
                                  const_castop castop_bitcast c p8)
    | _ => Some (const_castop castop_bitcast c p8,
                 const_castop castop_bitcast 
                   (const_gep false c 
                   (Cons_list_const (const_int Size.ThirtyTwo 
                   (INTEGER.of_Z 32%Z 1%Z false)) Nil_list_const)) p8)
    end
| const_gep _ pc _ => get_const_metadata pc
| const_castop castop_bitcast pc (typ_pointer _) => get_const_metadata pc
| _ => None
end.

Definition null_md := mkMD Mem.nullptr (Int.zero 31) (Int.zero 31).

Definition get_reg_metadata TD gl (rm:rmetadata) (v:value) : option metadata :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some md => Some md
      | _ => None
      end
  | value_const c => 
      match get_const_metadata c with
      | Some (bc, ec) => 
          match const2GV TD gl bc, const2GV TD gl ec with
          | Some ((Vptr bblk bofs, AST.Mint sz1)::nil), 
            Some ((Vptr eblk eofs, AST.Mint sz2)::nil) =>
             if zeq bblk eblk && eq_nat_dec sz1 31 && eq_nat_dec sz2 31 
             then ret (mkMD bblk bofs eofs) else None
          | _, _ => None 
          end
      | None => Some null_md
      end
  end.

Definition assert_mptr (TD:TargetData) (t:typ) (ptr:GenericValue) (md:metadata)
  : bool :=
  let 'mkMD bb bofs eofs := md in
  match (GV2ptr TD (getPointerSize TD) ptr, getTypeAllocSize TD t) with
  | (Some (Vptr pb pofs), Some tsz) =>
      zeq pb bb &&
      zle (Integers.Int.signed 31 bofs) (Integers.Int.signed 31 pofs) &&
      zle (Integers.Int.signed 31 pofs + Size.to_Z tsz) 
          (Integers.Int.signed 31 eofs)
  | _ => false
  end.  

Definition mmetadata := Values.block -> int32 -> option metadata.

Definition get_mem_metadata TD MM (gv:GenericValue) : metadata :=
  match (GV2ptr TD (getPointerSize TD) gv) with
  | Some (Vptr b ofs) => 
      match MM b ofs with
      | Some md => md
      | _ => null_md
      end
  | _ => null_md
  end.

Definition set_mem_metadata TD MM (gv:GenericValue) (md:metadata) 
  : mmetadata :=
  match (GV2ptr TD (getPointerSize TD) gv) with
  | Some (Vptr b ofs) => 
     fun b1 => fun ofs1 =>
       if zeq b1 b && Integers.Int.eq_dec 31 ofs ofs1 then Some md 
       else MM b1 ofs1
  | _ => MM
  end.

End SBspecAux.

Module SBspec. 

Export Opsem.
Export SBspecAux.

Section SBspec.

Context {GVsSig : GenericValues}.

Definition prop_reg_metadata lc rmd pid gvp (md:metadata) 
  : (@GVsMap GVsSig) * rmetadata :=
  (updateAddAL _ lc pid gvp, updateAddAL _ rmd pid md).

Notation GVs := GVsSig.(GVsT).
Definition GVsMap := list (id * GVs).
Notation "gv @ gvs" := 
  (GVsSig.(instantiate_gvs) gv gvs) (at level 43, right associativity).
Notation "$ gv # t $" := (GVsSig.(gv2gvs) gv t) (at level 41).
Notation "vidxs @@ vidxss" := (in_list_gvs vidxs vidxss) 
  (at level 43, right associativity).

Record ExecutionContext : Type := mkEC {
CurFunction : fdef;
CurBB       : block;
CurCmds     : cmds;                  (* cmds to run within CurBB *)
Terminator  : terminator;
Locals      : GVsMap;                (* LLVM values used in this invocation *)
Rmap        : rmetadata;
Allocas     : list mblock            (* Track memory allocated by alloca *)
}.

Definition ECStack := list ExecutionContext.

Record State : Type := mkState {
ECS                : ECStack;
Mem                : mem;
Mmap               : mmetadata
}.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (gl:GVMap) (lc:GVsMap) (rm:rmetadata) : 
  option (list (id * GVs * option metadata)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some v => 
      match (getOperandValue TD v lc gl, 
             getIncomingValuesForBlockFromPHINodes TD PNs b gl lc rm)
      with
      | (Some gv1, Some idgvs) => 
          if isPointerTypB t then
            match get_reg_metadata TD gl rm v with
            | Some md => Some ((id0,gv1,Some md)::idgvs)
            | None => None
            end
          else Some ((id0,gv1,None)::idgvs)
      | _ => None
      end               
  end
end.

Fixpoint updateValuesForNewBlock (ResultValues:list (id*GVs*option metadata)) 
  (lc:GVsMap) (rm:rmetadata) : GVsMap * rmetadata :=
match ResultValues with
| nil => (lc, rm)
| (id0, v, opmd)::ResultValues' => 
    let '(lc', rm') := updateValuesForNewBlock ResultValues' lc rm in
    match opmd with
    | None => (updateAddAL _ lc' id0 v, rm')
    | Some md => prop_reg_metadata lc' rm' id0 v md
    end
end.

Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) (PrevBB:block) 
  (gl:GVMap) (lc:GVsMap) (rm:rmetadata) : option (GVsMap * rmetadata) :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB gl lc rm with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues lc rm)
  | None => None
  end.

(*
  LLVM does not ensure that a function is called with its correct type. So 
  metadata may not be passed into or out from a function correctly. For example,
  if a function is of typ int* -> void, and used as typ void -> int*, then
  the callsite will not initialize metadata for its argument since the callsite
  thinks its signature is void -> void. Plus, the callsite cannot get any
  metadata from the function's return.

  In the semantics, we do not want to take such cases as stuck states, because
  1) the original LLVM semantics does not check the problem. 
  2) our SBpass does not check this issue dynamically either

  So, we let the values be undefined at these cases. Then, we can still prove
  preservation and progress with the same stuck states as LLVMopsem, since
  the undefined values do not ensure any safety. However, we should prove that
  the subset of instructions w/o call and ret can progress w/o memory violation.

  In implementation, the shadow stack interface does the similar things ---
  returning arbitrary values.
*)

Definition returnResult (TD:TargetData) (rt:typ) (Result:value) 
  (lc:GVsMap) (rm:rmetadata) (gl:GVMap) : option (GVs * metadata)
  :=
  match getOperandValue TD Result lc gl with
  | Some gr =>
      if isPointerTypB rt then
        match get_reg_metadata TD gl rm Result with
        | Some md => Some (gr, md)
        | None => None
        end
      else Some (gr, null_md)
  | _ => None
  end.

Definition returnUpdateLocals (TD:TargetData) (c':cmd) (rt:typ) (Result:value) 
  (lc lc':GVsMap) (rm rm':rmetadata) (gl:GVMap) : option (GVsMap * rmetadata) :=
  match returnResult TD rt Result lc rm gl with
  | Some (gr,md) =>
      match c' with
      | insn_call id0 false _ t _ _ =>
        match t with
        | typ_function ct _ _ =>
           match (GVsSig.(lift_op1) (fit_gv TD ct) gr ct) with
           | Some gr' => 
              if isPointerTypB ct then 
                Some (prop_reg_metadata lc' rm' id0 gr' md)
              else 
                Some (updateAddAL _ lc' id0 gr', rm')
           | _ => None
           end
        | _ => None
        end
      | insn_call _ _ _ _ _ _ => Some (lc', rm')
      | _ => None
      end
  | _ => None
  end.

Definition exCallUpdateLocals TD (ft:typ) (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVsMap) (rm:rmetadata) 
  : option (GVsMap*rmetadata) :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => 
          match ft with
          | typ_function t _ _ => 
            match fit_gv TD t Result with
            | Some gr =>
                if isPointerTypB t then
                     Some (updateAddAL _ lc rid ($ gr # t $), 
                           updateAddAL _ rm rid null_md)
                else Some (updateAddAL _ lc rid ($ gr # t $), rm)
            | _ => None
            end
          | _ => None
          end
      end
  | true => Some (lc, rm)
  end.

Fixpoint params2GVs (TD:TargetData) (lp:params) (lc:GVsMap) (gl:GVMap) 
  (rm:rmetadata) : option (list (GVs * option metadata)) :=
match lp with
| nil => Some nil
| ((t,_), v)::lp' => 
    match (getOperandValue TD v lc gl, params2GVs TD lp' lc gl rm) with
    | (Some gv, Some gvs) =>
       if isPointerTypB t then 
         Some ((gv, get_reg_metadata TD gl rm v)::gvs)
       else Some ((gv, None)::gvs)
    | _ => None
    end
end.

Fixpoint _initializeFrameValues TD (la:args) (lg:list (GVs*option metadata))
  (lc:GVsMap) (rm : rmetadata) : option (GVsMap * rmetadata) :=
match (la, lg) with
| ((t, _, id0)::la', (gv, opmd)::lg') => 
   match _initializeFrameValues TD la' lg' lc rm,
         GVsSig.(lift_op1) (fit_gv TD t) gv t with
   | Some (lc',rm'), Some gv' =>
     if isPointerTypB t then
       match opmd with
       | None => 
           Some (prop_reg_metadata lc' rm' id0 gv' null_md)
       | Some md => 
           Some (prop_reg_metadata lc' rm' id0 gv' md)
       end
     else Some (updateAddAL _ lc' id0 gv', rm')
   | _, _ => None
   end
| ((t, _, id0)::la', nil) => 
   match _initializeFrameValues TD la' nil lc rm, gundef TD t with
   | Some (lc',rm'), Some gv =>
     if isPointerTypB t then
       Some (prop_reg_metadata lc' rm' id0 ($ gv # t $) null_md)
     else Some (updateAddAL _ lc' id0 ($ gv # t $), rm')
   | _, _ => None
   end
| _ => Some (lc, rm)
end.

Definition initLocals TD (la:args) (lg:list (GVs*option metadata)) 
  : option (GVsMap * rmetadata) :=
_initializeFrameValues TD la lg nil nil.

Inductive sInsn_delta : Config -> State -> State -> Prop :=
| sReturn : forall S TD Ps F B rid RetTy Result lc rm gl fs F' B' c' cs' tmn' 
    lc' rm' EC Mem MM Mem' als als' lc'' rm'',   
  returnUpdateLocals TD c' RetTy Result lc lc' rm rm' gl = Some (lc'', rm'') ->
  sInsn_delta (mkCfg S TD Ps gl fs)
    (mkState 
      ((mkEC F B nil (insn_return rid RetTy Result) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) Mem MM)
    (mkState ((mkEC F' B' cs' tmn' lc'' rm'' als')::EC) Mem' MM)

| sReturnVoid : forall S TD Ps F B rid lc rm gl fs F' B' c' tmn' lc' rm' EC cs' 
    Mem MM Mem' als als',   
  sInsn_delta (mkCfg S TD Ps gl fs) 
    (mkState 
      ((mkEC F B nil (insn_return_void rid) lc rm als)::
       (mkEC F' B' (c'::cs') tmn' lc' rm' als')::EC) Mem MM)
    (mkState ((mkEC F' B' cs' tmn' lc' rm' als')::EC) Mem' MM)

| sBranch : forall S TD Ps F B lc rm gl fs bid Cond l1 l2 l' ps' cs' tmn' lc' 
    rm' EC Mem MM als,   
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B nil (insn_br bid Cond l1 l2) lc rm als)::EC) Mem MM)
    (mkState ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      Mem MM)

| sBranch_uncond : forall S TD Ps F B lc rm gl fs bid l l' ps' cs' tmn' lc' rm'
    EC Mem MM als,   
  switchToNewBasicBlock TD (block_intro l' ps' cs' tmn') B gl lc rm = 
    Some (lc', rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B nil (insn_br_uncond bid l) lc rm als)::EC) Mem MM)
    (mkState ((mkEC F (block_intro l' ps' cs' tmn') cs' tmn' lc' rm' als)::EC) 
      Mem MM)

| sBop: forall cfg F B lc rm id bop sz v1 v2 lc' EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState ((mkEC F B ((insn_bop id bop sz v1 v2)::cs) tmn lc rm als)::EC) 
      Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sFBop: forall cfg F B lc rm id fbop fp v1 v2 lc' EC cs tmn Mem MM 
    als,
  sInsn_delta cfg
    (mkState ((mkEC F B ((insn_fbop id fbop fp v1 v2)::cs) tmn lc rm als)::EC) 
      Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sExtractValue : forall cfg F B lc rm id t v lc' idxs EC cs tmn 
    Mem MM als,
  sInsn_delta cfg
    (mkState 
      ((mkEC F B ((insn_extractvalue id t v idxs)::cs) tmn lc rm als)::EC) 
      Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sInsertValue : forall cfg F B lc rm id t v t' v' lc' idxs 
    EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_insertvalue id t v t' v' idxs)::cs) tmn lc rm als)
      ::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sMalloc : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n gns,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id ($ (blk2GV TD mb) # typ_pointer t $) 
    (bound2MD mb tsz n) = (lc',rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState ((mkEC F B ((insn_malloc id t v align)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem' MM)

| sFree : forall cfg F B lc rm fid t v EC cs tmn Mem als Mem' MM,
  sInsn_delta cfg
    (mkState ((mkEC F B ((insn_free fid t v)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc rm als)::EC) Mem' MM)

| sAlloca : forall S TD Ps F B lc rm gl fs id t v gn align EC cs tmn Mem MM als 
    Mem' tsz mb lc' rm' n gns,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gns ->
  gn @ gns ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  GV2int TD Size.ThirtyTwo gn = Some n ->
  prop_reg_metadata lc rm id ($(blk2GV TD mb) # typ_pointer t$) 
    (bound2MD mb tsz n) = (lc',rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_alloca id t v align)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm' (mb::als))::EC) Mem' MM)

| sLoad_nptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem als 
    gvp gv MM md gvps,
  get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps ->
  assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  isPointerTypB t = false ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState
      ((mkEC F B cs tmn (updateAddAL _ lc id ($ gv # t $)) rm als)::EC) Mem MM)

| sLoad_ptr : forall S TD Ps F B lc rm gl fs id t align vp EC cs tmn Mem MM als 
    gvp gv md md' lc' rm' gvps,
  get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps ->
  assert_mptr TD t gvp md ->
  mload TD Mem gvp t align = Some gv ->
  isPointerTypB t = true ->
  get_mem_metadata TD MM gvp = md' -> 
  prop_reg_metadata lc rm id ($ gv # t $) md' = (lc', rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState 
      ((mkEC F B ((insn_load id t vp align)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem MM)

| sStore_nptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md Mem' gvps gvs,
  get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps -> gv @ gvs ->
  assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  isPointerTypB t = false ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc rm als)::EC) Mem' MM)

| sStore_ptr : forall S TD Ps F B lc rm gl fs sid t align v vp EC cs tmn Mem MM
    als gv gvp md md' Mem' MM' gvps gvs,
  get_reg_metadata TD gl rm vp = Some md ->
  getOperandValue TD v lc gl = Some gvs ->
  getOperandValue TD vp lc gl = Some gvps ->
  gvp @ gvps -> gv @ gvs ->
  assert_mptr TD t gvp md ->
  mstore TD Mem gvp t gv align = Some Mem' ->
  isPointerTypB t = true ->
  get_reg_metadata TD gl rm v = Some md' ->
  set_mem_metadata TD MM gvp md' = MM' -> 
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState 
      ((mkEC F B ((insn_store sid t v vp align)::cs) tmn lc rm als)::EC) Mem MM)
    (mkState ((mkEC F B cs tmn lc rm als)::EC) Mem' MM')

| sGEP : forall S TD Ps F B lc rm gl fs id inbounds t vp idxs EC  
                 cs tmn Mem MM als lc' rm' md,
  get_reg_metadata TD gl rm vp = Some md ->
  updateAddAL _ rm id md = rm' ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_gep id inbounds t vp idxs)::cs) tmn lc rm als)::EC) 
      Mem MM)
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem MM)

| sTrunc : forall cfg F B lc rm id truncop t1 v1 t2 lc' EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_trunc id truncop t1 v1 t2)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sExt : forall cfg F B lc rm id extop t1 v1 t2 lc' EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_ext id extop t1 v1 t2)::cs) tmn lc rm als)::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sBitcast_nptr : forall cfg F B lc rm id t1 v1 t2 lc' EC cs tmn Mem MM als,
  isPointerTypB t1 = false ->
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sBitcast_ptr : forall S TD Ps F B lc rm gl fs id t1 v1 t2 EC cs tmn Mem MM
    als md lc' rm',
  isPointerTypB t1 = true ->
  get_reg_metadata TD gl rm v1 = Some md ->
  updateAddAL _ rm id md = rm' ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_cast id castop_bitcast t1 v1 t2)::cs) tmn lc rm als)
        ::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem MM)

| sInttoptr : forall cfg F B lc rm id t1 v1 t2 EC cs tmn Mem MM als lc' rm',
  updateAddAL _ rm id null_md = rm' ->
  sInsn_delta cfg
    (mkState  
      ((mkEC F B ((insn_cast id castop_inttoptr t1 v1 t2)::cs) tmn lc rm als)
        ::EC) Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem MM)

| sOtherCast : forall cfg F B lc rm id castop t1 v1 t2 lc' EC cs tmn Mem MM als,
  castop <> castop_bitcast /\ castop <> castop_inttoptr ->
  sInsn_delta cfg  
    (mkState  
      ((mkEC F B ((insn_cast id castop t1 v1 t2)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sIcmp : forall cfg F B lc rm id cond t v1 v2 lc' EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_icmp id cond t v1 v2)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sFcmp : forall cfg F B lc rm id fcond fp v1 v2 lc' EC cs tmn Mem MM als,
  sInsn_delta cfg
    (mkState
      ((mkEC F B ((insn_fcmp id fcond fp v1 v2)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sSelect_nptr : forall cfg F B lc rm id v0 t v1 v2 EC cs tmn Mem MM als lc',
  isPointerTypB t = false ->
  sInsn_delta cfg
    (mkState 
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
       Mem MM) 
    (mkState ((mkEC F B cs tmn lc' rm als)::EC) Mem MM)

| sSelect_ptr : forall S TD Ps F B lc rm gl fs id v0 t v1 v2 c EC cs tmn Mem MM
    als gv1 gv2 md1 md2 cond,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  c @ cond ->
  isPointerTypB t = true ->
  get_reg_metadata TD gl rm v1 = Some md1 ->
  get_reg_metadata TD gl rm v2 = Some md2 ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState
      ((mkEC F B ((insn_select id v0 t v1 v2)::cs) tmn lc rm als)::EC) 
      Mem MM) 
    (mkState
      ((mkEC F B cs tmn 
        (if isGVZero TD c 
         then updateAddAL _ lc id gv2
         else updateAddAL _ lc id gv1)
        (if isGVZero TD c 
         then updateAddAL _ rm id md2
         else updateAddAL _ rm id md1)
        als)::EC) 
      Mem MM)

| sCall : forall S TD Ps F B lc rm gl fs rid noret ca fid fv lp cs tmn ogvs
             ft l' ps' cs' tmn' EC fa rt la va lb Mem MM als rm' lc',
  (* only look up the current module for the time being, 
     do not support linkage. *)
  params2GVs TD lp lc gl rm = Some ogvs ->
  initLocals TD la ogvs = Some (lc', rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState 
      ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
        ::EC) Mem MM)
    (mkState 
      ((mkEC (fdef_intro (fheader_intro fa rt fid la va) lb) 
                (block_intro l' ps' cs' tmn') cs' tmn' 
                lc' rm' nil)::
       (mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
         ::EC) Mem MM)

| sExCall : forall S TD Ps F B lc rm gl fs rid noret ca fid fv lp cs tmn EC 
           gvss fptr fptrs rt fa ft la va Mem als oresult Mem' lc' rm' MM gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  getOperandValue TD fv lc gl = Some fptrs -> 
  fptr @ fptrs -> 
  lookupExFdecViaPtr Ps fs fptr = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  Opsem.params2GVs TD lp lc gl = Some gvss ->
  gvs @@ gvss ->
  callExternalFunction Mem fid gvs = Some (oresult, Mem') ->
  exCallUpdateLocals TD ft noret rid oresult lc rm = Some (lc',rm') ->
  sInsn_delta (mkCfg S TD Ps gl fs)  
    (mkState  
      ((mkEC F B ((insn_call rid noret ca ft fv lp)::cs) tmn lc rm als)
       ::EC) Mem MM)
    (mkState ((mkEC F B cs tmn lc' rm' als)::EC) Mem' MM)
.

Definition s_isFinialState (state:State) : bool :=
match state with
| (mkState ((mkEC _ _ nil (insn_return_void _) _ _ _)::nil) _ _) => true
| (mkState ((mkEC _ _ nil (insn_return _ _ _) _ _ _)::nil) _ _) => true 
| _ => false
end.

Definition sbEC__EC (ec : ExecutionContext) : Opsem.ExecutionContext :=
let '(mkEC f b cs tmn lc _ als) := ec in
Opsem.mkEC f b cs tmn lc als.

Definition sbECs__ECs (ecs : ECStack) : Opsem.ECStack := 
List.map sbEC__EC ecs.

Definition sbState__State (st : State) : Opsem.State :=
let '(mkState ecs M _) := st in
Opsem.mkState (sbECs__ECs ecs) M.

Inductive sInsn : Config -> State -> State -> trace -> Prop :=
| sInsn_intro : forall cfg S1 S2 tr,
    sInsn_delta cfg S1 S2 ->
    Opsem.sInsn cfg (sbState__State S1) (sbState__State S2) tr ->
    sInsn cfg S1 S2 tr.

Inductive sop_star : Config -> State -> State -> trace -> Prop :=
| sop_star_nil : forall cfg state, sop_star cfg state state trace_nil
| sop_star_cons : forall cfg state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_star cfg state1 state3 (trace_app tr1 tr2)
.

Inductive sop_plus : Config -> State -> State -> trace -> Prop :=
| sop_plus_cons : forall cfg state1 state2 state3 tr1 tr2,
    sInsn cfg state1 state2 tr1 ->
    sop_star cfg state2 state3 tr2 ->
    sop_plus cfg state1 state3 (trace_app tr1 tr2)
.

CoInductive sop_diverges : Config -> State -> Trace -> Prop :=
| sop_diverges_intro : forall cfg state1 state2 tr1 tr2,
    sop_plus cfg state1 state2 tr1 ->
    sop_diverges cfg state2 tr2 ->
    sop_diverges cfg state1 (Trace_app tr1 tr2)
.

End SBspec. 

Ltac invert_prop_reg_metadata :=
  match goal with
  | [H : prop_reg_metadata _ _ _ _ _ = (_, _) |- _ ] =>
      inversion H; subst; eauto
  end.

Hint Constructors sInsn_delta sInsn sop_star sop_plus.

End SBspec.

Tactic Notation "sb_sInsn_cases" tactic(first) tactic(c) :=
  first;
  [ c "sReturn" | c "sReturnVoid" | c "sBranch" | c "sBranch_uncond" |
    c "sBop" | c "sFBop" | c "sExtractValue" | c "sInsertValue" |
    c "sMalloc" | c "sFree" | c "sAlloca" | 
    c "sLoad_nptr" | c "sLoad_ptr" | 
    c "sStore_nptr" | c "sStore_ptr" | 
    c "sGEP" | c "sTrunc" | c "sExt" | 
    c "sBitcast_nptr" | c "sBitcast_ptr" | c "sInttoptr" | c "sOthercast" | 
    c "sIcmp" | c "sFcmp" | 
    c "sSelect_nptr" | c "sSelect_ptr" |  
    c "sCall" | c "sExCall" ].


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)


