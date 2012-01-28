open BinInt
open BinPos
open Coqlib
open Datatypes
open Integers
open List0
open Memory
open MetatheoryAtom
open Values
open Alist
open Genericvalues
open Infrastructure
open Syntax
open Targetdata

module SBspecAux = 
 struct 
  type metadata = { md_blk : block; md_bofs : Int.int; md_eofs : Int.int }
  
  (** val metadata_rect :
      (block -> Int.int -> Int.int -> 'a1) -> metadata -> 'a1 **)
  
  let metadata_rect f m =
    let { md_blk = x; md_bofs = x0; md_eofs = x1 } = m in f x x0 x1
  
  (** val metadata_rec :
      (block -> Int.int -> Int.int -> 'a1) -> metadata -> 'a1 **)
  
  let metadata_rec f m =
    let { md_blk = x; md_bofs = x0; md_eofs = x1 } = m in f x x0 x1
  
  (** val md_blk : metadata -> block **)
  
  let md_blk x = x.md_blk
  
  (** val md_bofs : metadata -> Int.int **)
  
  let md_bofs x = x.md_bofs
  
  (** val md_eofs : metadata -> Int.int **)
  
  let md_eofs x = x.md_eofs
  
  type rmetadata = (LLVMsyntax.id*metadata) list
  
  (** val bound2MD : LLVMgv.mblock -> LLVMsyntax.sz -> coq_Z -> metadata **)
  
  let bound2MD = Softbound_aux.bound2MD
  
  (** val i8 : LLVMsyntax.typ **)
  
  let i8 =
    LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_Eight
  
  (** val p8 : LLVMsyntax.typ **)
  
  let p8 =
    LLVMsyntax.Coq_typ_pointer i8
  
  (** val get_const_metadata :
      LLVMsyntax.const -> (LLVMsyntax.const*LLVMsyntax.const) option **)
  
  let rec get_const_metadata c = match c with
    | LLVMsyntax.Coq_const_gid (t, gid) ->
        (match t with
           | LLVMsyntax.Coq_typ_function (t0, l, v) -> Some
               ((LLVMsyntax.Coq_const_castop (LLVMsyntax.Coq_castop_bitcast,
               c, p8)),(LLVMsyntax.Coq_const_castop
               (LLVMsyntax.Coq_castop_bitcast, c, p8)))
           | _ -> Some ((LLVMsyntax.Coq_const_castop
               (LLVMsyntax.Coq_castop_bitcast, c,
               p8)),(LLVMsyntax.Coq_const_castop
               (LLVMsyntax.Coq_castop_bitcast, (LLVMsyntax.Coq_const_gep
               (false, c, (LLVMsyntax.Cons_list_const
               ((LLVMsyntax.Coq_const_int (LLVMsyntax.Size.coq_ThirtyTwo,
               (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                 (Coq_xO Coq_xH)))))) (Zpos Coq_xH) false))),
               LLVMsyntax.Nil_list_const)))), p8))))
    | LLVMsyntax.Coq_const_castop (c0, pc, t) ->
        (match c0 with
           | LLVMsyntax.Coq_castop_bitcast ->
               (match t with
                  | LLVMsyntax.Coq_typ_pointer t0 -> get_const_metadata pc
                  | _ -> None)
           | _ -> None)
    | LLVMsyntax.Coq_const_gep (i, pc, l) -> get_const_metadata pc
    | _ -> None
  
  (** val null_md : metadata **)
  
  let null_md =
    { md_blk = Mem.nullptr; md_bofs =
      (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))));
      md_eofs =
      (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) }
  
  (** val get_reg_metadata :
      LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap -> rmetadata ->
      LLVMsyntax.value -> metadata option **)
  
  let get_reg_metadata = Softbound_aux.get_reg_metadata
  
  (** val assert_mptr :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> LLVMgv.coq_GenericValue ->
      metadata -> bool **)
  
  let assert_mptr tD t ptr md =
    let { md_blk = bb; md_bofs = bofs; md_eofs = eofs } = md in
    let o = LLVMgv.coq_GV2ptr tD (LLVMtd.getPointerSize tD) ptr in
    let o0 = LLVMtd.getTypeAllocSize tD t in
    (match o with
       | Some v ->
           (match v with
              | Vptr (pb, pofs) ->
                  (match o0 with
                     | Some tsz ->
                         if if proj_sumbool (zeq pb bb)
                            then proj_sumbool
                                   (zle
                                     (Int.signed (S (S (S (S (S (S (S (S (S
                                       (S (S (S (S (S (S (S (S (S (S (S (S (S
                                       (S (S (S (S (S (S (S (S (S
                                       O))))))))))))))))))))))))))))))) bofs)
                                     (Int.signed (S (S (S (S (S (S (S (S (S
                                       (S (S (S (S (S (S (S (S (S (S (S (S (S
                                       (S (S (S (S (S (S (S (S (S
                                       O))))))))))))))))))))))))))))))) pofs))
                            else false
                         then proj_sumbool
                                (zle
                                  (coq_Zplus
                                    (Int.signed (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S
                                      O))))))))))))))))))))))))))))))) pofs)
                                    (LLVMsyntax.Size.to_Z tsz))
                                  (Int.signed (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S
                                    O))))))))))))))))))))))))))))))) eofs))
                         else false
                     | None -> false)
              | _ -> false)
       | None -> false)
  
  type mmetadata = block -> Int.int -> metadata option
  
  (** val get_mem_metadata :
      LLVMtd.coq_TargetData -> (block -> Int.int -> metadata option) ->
      LLVMgv.coq_GenericValue -> metadata **)
  
  let get_mem_metadata tD mM gv =
    match LLVMgv.coq_GV2ptr tD (LLVMtd.getPointerSize tD) gv with
      | Some v ->
          (match v with
             | Vptr (b, ofs) ->
                 (match mM b ofs with
                    | Some md -> md
                    | None -> null_md)
             | _ -> null_md)
      | None -> null_md
  
  (** val set_mem_metadata :
      LLVMtd.coq_TargetData -> mmetadata -> LLVMgv.coq_GenericValue ->
      metadata -> mmetadata **)
  
  let set_mem_metadata tD mM gv md =
    match LLVMgv.coq_GV2ptr tD (LLVMtd.getPointerSize tD) gv with
      | Some v ->
          (match v with
             | Vptr (b, ofs) -> (fun b1 ofs1 ->
                 if if proj_sumbool (zeq b1 b)
                    then proj_sumbool
                           (Int.eq_dec (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S O))))))))))))))))))))))))))))))) ofs ofs1)
                    else false
                 then Some md
                 else mM b1 ofs1)
             | _ -> mM)
      | None -> mM
 end

module SBspec = 
 struct 
  (** val prop_reg_metadata :
      Opsem.coq_GenericValues -> Opsem.coq_GVsT coq_AssocList ->
      SBspecAux.metadata coq_AssocList -> AtomImpl.atom -> Opsem.coq_GVsT ->
      SBspecAux.metadata -> Opsem.Opsem.coq_GVsMap*SBspecAux.rmetadata **)
  
  let prop_reg_metadata gVsSig lc rmd pid gvp md =
    (updateAddAL lc pid gvp),(updateAddAL rmd pid md)
  
  type coq_GVsMap = (LLVMsyntax.id*Opsem.coq_GVsT) list
  
  type coq_ExecutionContext = { coq_CurFunction : LLVMsyntax.fdef;
                                coq_CurBB : LLVMsyntax.block;
                                coq_CurCmds : LLVMsyntax.cmds;
                                coq_Terminator : LLVMsyntax.terminator;
                                coq_Locals : coq_GVsMap;
                                coq_Rmap : SBspecAux.rmetadata;
                                coq_Allocas : LLVMgv.mblock list }
  
  (** val coq_ExecutionContext_rect :
      Opsem.coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
      LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap ->
      SBspecAux.rmetadata -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rect gVsSig f e =
    let { coq_CurFunction = x; coq_CurBB = x0; coq_CurCmds = x1;
      coq_Terminator = x2; coq_Locals = x3; coq_Rmap = x4; coq_Allocas =
      x5 } = e
    in
    f x x0 x1 x2 x3 x4 x5
  
  (** val coq_ExecutionContext_rec :
      Opsem.coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
      LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap ->
      SBspecAux.rmetadata -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rec gVsSig f e =
    let { coq_CurFunction = x; coq_CurBB = x0; coq_CurCmds = x1;
      coq_Terminator = x2; coq_Locals = x3; coq_Rmap = x4; coq_Allocas =
      x5 } = e
    in
    f x x0 x1 x2 x3 x4 x5
  
  (** val coq_CurFunction :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.fdef **)
  
  let coq_CurFunction _ x = x.coq_CurFunction
  
  (** val coq_CurBB :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.block **)
  
  let coq_CurBB _ x = x.coq_CurBB
  
  (** val coq_CurCmds :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.cmds **)
  
  let coq_CurCmds _ x = x.coq_CurCmds
  
  (** val coq_Terminator :
      Opsem.coq_GenericValues -> coq_ExecutionContext ->
      LLVMsyntax.terminator **)
  
  let coq_Terminator _ x = x.coq_Terminator
  
  (** val coq_Locals :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> coq_GVsMap **)
  
  let coq_Locals _ x = x.coq_Locals
  
  (** val coq_Rmap :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> SBspecAux.rmetadata **)
  
  let coq_Rmap _ x = x.coq_Rmap
  
  (** val coq_Allocas :
      Opsem.coq_GenericValues -> coq_ExecutionContext -> LLVMgv.mblock list **)
  
  let coq_Allocas _ x = x.coq_Allocas
  
  type coq_ECStack = coq_ExecutionContext list
  
  type coq_State = { coq_ECS : coq_ECStack; coq_Mem : 
                     LLVMgv.mem; coq_Mmap : SBspecAux.mmetadata }
  
  (** val coq_State_rect :
      Opsem.coq_GenericValues -> (coq_ECStack -> LLVMgv.mem ->
      SBspecAux.mmetadata -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rect gVsSig f s =
    let { coq_ECS = x; coq_Mem = x0; coq_Mmap = x1 } = s in f x x0 x1
  
  (** val coq_State_rec :
      Opsem.coq_GenericValues -> (coq_ECStack -> LLVMgv.mem ->
      SBspecAux.mmetadata -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rec gVsSig f s =
    let { coq_ECS = x; coq_Mem = x0; coq_Mmap = x1 } = s in f x x0 x1
  
  (** val coq_ECS : Opsem.coq_GenericValues -> coq_State -> coq_ECStack **)
  
  let coq_ECS _ x = x.coq_ECS
  
  (** val coq_Mem : Opsem.coq_GenericValues -> coq_State -> LLVMgv.mem **)
  
  let coq_Mem _ x = x.coq_Mem
  
  (** val coq_Mmap :
      Opsem.coq_GenericValues -> coq_State -> SBspecAux.mmetadata **)
  
  let coq_Mmap _ x = x.coq_Mmap
  
  (** val getIncomingValuesForBlockFromPHINodes :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.phinode
      list -> LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap ->
      SBspecAux.rmetadata ->
      ((LLVMsyntax.id*Opsem.coq_GVsT)*SBspecAux.metadata option) list option **)
  
  let rec getIncomingValuesForBlockFromPHINodes gVsSig tD pNs b gl lc rm =
    match pNs with
      | [] -> Some []
      | p::pNs0 ->
          let LLVMsyntax.Coq_insn_phi (id0, t, vls) = p in
          (match LLVMinfra.getValueViaBlockFromPHINode
                   (LLVMsyntax.Coq_insn_phi (id0, t, vls)) b with
             | Some v ->
                 (match Opsem.Opsem.getOperandValue gVsSig tD v lc gl with
                    | Some gv1 ->
                        (match getIncomingValuesForBlockFromPHINodes gVsSig
                                 tD pNs0 b gl lc rm with
                           | Some idgvs ->
                               if LLVMinfra.isPointerTypB t
                               then (match SBspecAux.get_reg_metadata tD gl
                                             rm v with
                                       | Some md -> Some (((id0,gv1),(Some
                                           md))::idgvs)
                                       | None -> None)
                               else Some (((id0,gv1),None)::idgvs)
                           | None -> None)
                    | None -> None)
             | None -> None)
  
  (** val updateValuesForNewBlock :
      Opsem.coq_GenericValues ->
      ((LLVMsyntax.id*Opsem.coq_GVsT)*SBspecAux.metadata option) list ->
      coq_GVsMap -> SBspecAux.rmetadata -> coq_GVsMap*SBspecAux.rmetadata **)
  
  let rec updateValuesForNewBlock gVsSig resultValues lc rm =
    match resultValues with
      | [] -> lc,rm
      | p::resultValues' ->
          let p0,opmd = p in
          let id0,v = p0 in
          let lc',rm' = updateValuesForNewBlock gVsSig resultValues' lc rm in
          (match opmd with
             | Some md -> prop_reg_metadata gVsSig lc' rm' id0 v md
             | None -> (updateAddAL lc' id0 v),rm')
  
  (** val switchToNewBasicBlock :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.block ->
      LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap ->
      SBspecAux.rmetadata -> (coq_GVsMap*SBspecAux.rmetadata) option **)
  
  let switchToNewBasicBlock gVsSig tD dest prevBB gl lc rm =
    let pNs = LLVMinfra.getPHINodesFromBlock dest in
    (match getIncomingValuesForBlockFromPHINodes gVsSig tD pNs prevBB gl lc
             rm with
       | Some resultValues -> Some
           (updateValuesForNewBlock gVsSig resultValues lc rm)
       | None -> None)
  
  (** val returnResult :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
      LLVMsyntax.value -> coq_GVsMap -> SBspecAux.rmetadata ->
      LLVMgv.coq_GVMap -> (Opsem.coq_GVsT*SBspecAux.metadata) option **)
  
  let returnResult gVsSig tD rt result lc rm gl =
    match Opsem.Opsem.getOperandValue gVsSig tD result lc gl with
      | Some gr ->
          if LLVMinfra.isPointerTypB rt
          then (match SBspecAux.get_reg_metadata tD gl rm result with
                  | Some md -> Some (gr,md)
                  | None -> None)
          else Some (gr,SBspecAux.null_md)
      | None -> None
  
  (** val returnUpdateLocals :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.cmd ->
      LLVMsyntax.typ -> LLVMsyntax.value -> coq_GVsMap -> coq_GVsMap ->
      SBspecAux.rmetadata -> SBspecAux.rmetadata -> LLVMgv.coq_GVMap ->
      (coq_GVsMap*SBspecAux.rmetadata) option **)
  
  let returnUpdateLocals gVsSig tD c' rt result lc lc' rm rm' gl =
    match returnResult gVsSig tD rt result lc rm gl with
      | Some p ->
          let gr,md = p in
          (match c' with
             | LLVMsyntax.Coq_insn_call (id0, n, c, t, v, p0) ->
                 if n
                 then Some (lc',rm')
                 else (match t with
                         | LLVMsyntax.Coq_typ_function (
                             ct, l, v0) ->
                             (match gVsSig.Opsem.lift_op1
                                      (LLVMgv.fit_gv tD ct) gr ct with
                                | Some gr' ->
                                    if LLVMinfra.isPointerTypB ct
                                    then Some
                                           (prop_reg_metadata gVsSig lc' rm'
                                             id0 gr' md)
                                    else Some ((updateAddAL lc' id0 gr'),rm')
                                | None -> None)
                         | _ -> None)
             | _ -> None)
      | None -> None
  
  (** val exCallUpdateLocals :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
      bool -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option -> coq_GVsMap
      -> SBspecAux.rmetadata -> (coq_GVsMap*SBspecAux.rmetadata) option **)
  
  let exCallUpdateLocals gVsSig tD ft noret rid oResult lc rm =
    if noret
    then Some (lc,rm)
    else (match oResult with
            | Some result ->
                (match ft with
                   | LLVMsyntax.Coq_typ_function (t, l, v) ->
                       (match LLVMgv.fit_gv tD t result with
                          | Some gr ->
                              if LLVMinfra.isPointerTypB t
                              then Some
                                     ((updateAddAL lc rid
                                        (gVsSig.Opsem.gv2gvs gr t)),
                                     (updateAddAL rm rid SBspecAux.null_md))
                              else Some
                                     ((updateAddAL lc rid
                                        (gVsSig.Opsem.gv2gvs gr t)),rm)
                          | None -> None)
                   | _ -> None)
            | None -> None)
  
  (** val params2GVs :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.params
      -> coq_GVsMap -> LLVMgv.coq_GVMap -> SBspecAux.rmetadata ->
      (Opsem.coq_GVsT*SBspecAux.metadata option) list option **)
  
  let rec params2GVs gVsSig tD lp lc gl rm =
    match lp with
      | [] -> Some []
      | p::lp' ->
          let p0,v = p in
          let t,a = p0 in
          (match Opsem.Opsem.getOperandValue gVsSig tD v lc gl with
             | Some gv ->
                 (match params2GVs gVsSig tD lp' lc gl rm with
                    | Some gvs ->
                        if LLVMinfra.isPointerTypB t
                        then Some
                               ((gv,(SBspecAux.get_reg_metadata tD gl rm v))::gvs)
                        else Some ((gv,None)::gvs)
                    | None -> None)
             | None -> None)
  
  (** val _initializeFrameValues :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
      (Opsem.coq_GVsT*SBspecAux.metadata option) list -> coq_GVsMap ->
      SBspecAux.rmetadata -> (coq_GVsMap*SBspecAux.rmetadata) option **)
  
  let rec _initializeFrameValues gVsSig tD la lg lc rm =
    match la with
      | [] -> Some (lc,rm)
      | p::la' ->
          let p0,id0 = p in
          let t,a = p0 in
          (match lg with
             | [] ->
                 (match _initializeFrameValues gVsSig tD la' [] lc rm with
                    | Some p1 ->
                        let lc',rm' = p1 in
                        (match LLVMgv.gundef tD t with
                           | Some gv ->
                               if LLVMinfra.isPointerTypB t
                               then Some
                                      (prop_reg_metadata gVsSig lc' rm' id0
                                        (gVsSig.Opsem.gv2gvs gv t)
                                        SBspecAux.null_md)
                               else Some
                                      ((updateAddAL lc' id0
                                         (gVsSig.Opsem.gv2gvs gv t)),rm')
                           | None -> None)
                    | None -> None)
             | p1::lg' ->
                 let gv,opmd = p1 in
                 (match _initializeFrameValues gVsSig tD la' lg' lc rm with
                    | Some p2 ->
                        let lc',rm' = p2 in
                        (match gVsSig.Opsem.lift_op1 
                                 (LLVMgv.fit_gv tD t) gv t with
                           | Some gv' ->
                               if LLVMinfra.isPointerTypB t
                               then (match opmd with
                                       | Some md -> Some
                                           (prop_reg_metadata gVsSig lc' rm'
                                             id0 gv' md)
                                       | None -> Some
                                           (prop_reg_metadata gVsSig lc' rm'
                                             id0 gv' SBspecAux.null_md))
                               else Some ((updateAddAL lc' id0 gv'),rm')
                           | None -> None)
                    | None -> None))
  
  (** val initLocals :
      Opsem.coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
      (Opsem.coq_GVsT*SBspecAux.metadata option) list ->
      (coq_GVsMap*SBspecAux.rmetadata) option **)
  
  let initLocals gVsSig tD la lg =
    _initializeFrameValues gVsSig tD la lg [] []
  
  (** val s_isFinialState : Opsem.coq_GenericValues -> coq_State -> bool **)
  
  let s_isFinialState gVsSig state =
    let { coq_ECS = eCS; coq_Mem = mem0; coq_Mmap = mmap } = state in
    (match eCS with
       | [] -> false
       | e::l ->
           let { coq_CurFunction = curFunction; coq_CurBB = curBB;
             coq_CurCmds = curCmds; coq_Terminator = terminator0;
             coq_Locals = locals; coq_Rmap = rmap; coq_Allocas = allocas } =
             e
           in
           (match curCmds with
              | [] ->
                  (match terminator0 with
                     | LLVMsyntax.Coq_insn_return (
                         i, t, v) ->
                         (match l with
                            | [] -> true
                            | e0::l0 -> false)
                     | LLVMsyntax.Coq_insn_return_void i ->
                         (match l with
                            | [] -> true
                            | e0::l0 -> false)
                     | _ -> false)
              | c::l0 -> false))
  
  (** val sbEC__EC :
      Opsem.coq_GenericValues -> coq_ExecutionContext ->
      Opsem.Opsem.coq_ExecutionContext **)
  
  let sbEC__EC gVsSig ec =
    let { coq_CurFunction = f; coq_CurBB = b; coq_CurCmds = cs;
      coq_Terminator = tmn; coq_Locals = lc; coq_Rmap = rmap; coq_Allocas =
      als } = ec
    in
    { Opsem.Opsem.coq_CurFunction = f; Opsem.Opsem.coq_CurBB = b;
    Opsem.Opsem.coq_CurCmds = cs; Opsem.Opsem.coq_Terminator = tmn;
    Opsem.Opsem.coq_Locals = lc; Opsem.Opsem.coq_Allocas = als }
  
  (** val sbECs__ECs :
      Opsem.coq_GenericValues -> coq_ECStack -> Opsem.Opsem.coq_ECStack **)
  
  let sbECs__ECs gVsSig ecs =
    map (sbEC__EC gVsSig) ecs
  
  (** val sbState__State :
      Opsem.coq_GenericValues -> coq_State -> Opsem.Opsem.coq_State **)
  
  let sbState__State gVsSig st =
    let { coq_ECS = ecs; coq_Mem = m; coq_Mmap = mmap } = st in
    { Opsem.Opsem.coq_ECS = (sbECs__ECs gVsSig ecs); Opsem.Opsem.coq_Mem =
    m }
 end

