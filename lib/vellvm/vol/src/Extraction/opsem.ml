open Alist
open Genericvalues
open Infrastructure
open Monad
open Syntax
open Targetdata

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_GenericValues = { cgv2gvs : (LLVMgv.coq_GenericValue ->
                                     LLVMsyntax.typ -> __);
                           gv2gvs : (LLVMgv.coq_GenericValue ->
                                    LLVMsyntax.typ -> __);
                           lift_op1 : ((LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue option) -> __
                                      -> LLVMsyntax.typ -> __ option);
                           lift_op2 : ((LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue ->
                                      LLVMgv.coq_GenericValue option) -> __
                                      -> __ -> LLVMsyntax.typ -> __ option) }

(** val coq_GenericValues_rect :
    (__ -> __ -> __ -> (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
    (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
    ((LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ ->
    LLVMsyntax.typ -> __ option) -> ((LLVMgv.coq_GenericValue ->
    LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ -> __ ->
    LLVMsyntax.typ -> __ option) -> __ -> __ -> __ -> __ -> __ -> __ -> __ ->
    __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> coq_GenericValues -> 'a1 **)

let coq_GenericValues_rect f g =
  let { cgv2gvs = x; gv2gvs = x0; lift_op1 = x1; lift_op2 = x2 } = g in
  f __ __ __ x x0 x1 x2 __ __ __ __ __ __ __ __ __ __ __ __ __

(** val coq_GenericValues_rec :
    (__ -> __ -> __ -> (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
    (LLVMgv.coq_GenericValue -> LLVMsyntax.typ -> __) ->
    ((LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ ->
    LLVMsyntax.typ -> __ option) -> ((LLVMgv.coq_GenericValue ->
    LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue option) -> __ -> __ ->
    LLVMsyntax.typ -> __ option) -> __ -> __ -> __ -> __ -> __ -> __ -> __ ->
    __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> coq_GenericValues -> 'a1 **)

let coq_GenericValues_rec f g =
  let { cgv2gvs = x; gv2gvs = x0; lift_op1 = x1; lift_op2 = x2 } = g in
  f __ __ __ x x0 x1 x2 __ __ __ __ __ __ __ __ __ __ __ __ __

type coq_GVsT = __

(** val cgv2gvs :
    coq_GenericValues -> LLVMgv.coq_GenericValue -> LLVMsyntax.typ ->
    coq_GVsT **)

let cgv2gvs x = x.cgv2gvs

(** val gv2gvs :
    coq_GenericValues -> LLVMgv.coq_GenericValue -> LLVMsyntax.typ ->
    coq_GVsT **)

let gv2gvs x = x.gv2gvs

(** val lift_op1 :
    coq_GenericValues -> (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue
    option) -> coq_GVsT -> LLVMsyntax.typ -> coq_GVsT option **)

let lift_op1 x = x.lift_op1

(** val lift_op2 :
    coq_GenericValues -> (LLVMgv.coq_GenericValue -> LLVMgv.coq_GenericValue
    -> LLVMgv.coq_GenericValue option) -> coq_GVsT -> coq_GVsT ->
    LLVMsyntax.typ -> coq_GVsT option **)

let lift_op2 x = x.lift_op2

module OpsemAux = 
 struct 
  (** val lookupFdefViaGVFromFunTable :
      LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue -> LLVMsyntax.id option **)
  
  let rec lookupFdefViaGVFromFunTable = Llvmcaml.GenericValue.lookupFdefViaGVFromFunTable
  
  (** val lookupFdefViaPtr :
      LLVMsyntax.products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue ->
      LLVMsyntax.fdef option **)
  
  let lookupFdefViaPtr ps fs fptr =
    mbind (fun fn -> LLVMinfra.lookupFdefViaIDFromProducts ps fn)
      (lookupFdefViaGVFromFunTable fs fptr)
  
  (** val lookupExFdecViaPtr :
      LLVMsyntax.products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue ->
      LLVMsyntax.fdec option **)
  
  let lookupExFdecViaPtr ps fs fptr =
    mbind (fun fn ->
      match LLVMinfra.lookupFdefViaIDFromProducts ps fn with
        | Some f -> None
        | None -> LLVMinfra.lookupFdecViaIDFromProducts ps fn)
      (lookupFdefViaGVFromFunTable fs fptr)
  
  (** val callExternalFunction :
      LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue list ->
      (LLVMgv.coq_GenericValue option*LLVMgv.mem) option **)
  
  let callExternalFunction = Llvmcaml.GenericValue.callExternalFunction
  
  (** val initGlobal :
      LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap -> LLVMgv.mem ->
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.const -> LLVMsyntax.align
      -> (LLVMgv.coq_GenericValue*LLVMgv.mem) option **)
  
  let initGlobal = Llvmcaml.GenericValue.initGlobal
  
  (** val initTargetData :
      LLVMsyntax.layouts -> LLVMsyntax.namedts -> LLVMgv.mem ->
      LLVMtd.coq_TargetData **)
  
  let initTargetData = Llvmcaml.GenericValue.initTargetData
  
  (** val getExternalGlobal :
      LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option **)
  
  let getExternalGlobal = Llvmcaml.GenericValue.getExternalGlobal
  
  (** val initFunTable :
      LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue option **)
  
  let initFunTable = Llvmcaml.GenericValue.initFunTable
  
  (** val genGlobalAndInitMem :
      LLVMtd.coq_TargetData -> LLVMsyntax.product list -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap -> LLVMgv.mem ->
      ((LLVMgv.coq_GVMap*LLVMgv.coq_GVMap)*LLVMgv.mem) option **)
  
  let rec genGlobalAndInitMem tD ps gl fs mem0 =
    match ps with
      | [] -> Some ((gl,fs),mem0)
      | p::ps' ->
          (match p with
             | LLVMsyntax.Coq_product_gvar g ->
                 (match g with
                    | LLVMsyntax.Coq_gvar_intro
                        (id0, l, spec, t, c, align0) ->
                        (match initGlobal tD gl mem0 id0 t c align0 with
                           | Some p0 ->
                               let gv,mem' = p0 in
                               genGlobalAndInitMem tD ps'
                                 (updateAddAL gl id0 gv) fs mem'
                           | None -> None)
                    | LLVMsyntax.Coq_gvar_external (
                        id0, spec, t) ->
                        (match getExternalGlobal mem0 id0 with
                           | Some gv ->
                               genGlobalAndInitMem tD ps'
                                 (updateAddAL gl id0 gv) fs mem0
                           | None -> None))
             | LLVMsyntax.Coq_product_fdec f ->
                 let LLVMsyntax.Coq_fheader_intro (f0, t, id0, a, v) = f in
                 (match initFunTable mem0 id0 with
                    | Some gv ->
                        genGlobalAndInitMem tD ps' 
                          (updateAddAL gl id0 gv) (updateAddAL fs id0 gv)
                          mem0
                    | None -> None)
             | LLVMsyntax.Coq_product_fdef f ->
                 let LLVMsyntax.Coq_fdef_intro (f0, b) = f in
                 let LLVMsyntax.Coq_fheader_intro (f1, t, id0, a, v) = f0 in
                 (match initFunTable mem0 id0 with
                    | Some gv ->
                        genGlobalAndInitMem tD ps' 
                          (updateAddAL gl id0 gv) (updateAddAL fs id0 gv)
                          mem0
                    | None -> None))
  
  type coq_Config = { coq_CurSystem : LLVMsyntax.system;
                      coq_CurTargetData : LLVMtd.coq_TargetData;
                      coq_CurProducts : LLVMsyntax.product list;
                      coq_Globals : LLVMgv.coq_GVMap;
                      coq_FunTable : LLVMgv.coq_GVMap }
  
  (** val coq_Config_rect :
      (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list
      -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> 'a1) -> coq_Config -> 'a1 **)
  
  let coq_Config_rect f c =
    let { coq_CurSystem = x; coq_CurTargetData = x0; coq_CurProducts = x1;
      coq_Globals = x2; coq_FunTable = x3 } = c
    in
    f x x0 x1 x2 x3
  
  (** val coq_Config_rec :
      (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list
      -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> 'a1) -> coq_Config -> 'a1 **)
  
  let coq_Config_rec f c =
    let { coq_CurSystem = x; coq_CurTargetData = x0; coq_CurProducts = x1;
      coq_Globals = x2; coq_FunTable = x3 } = c
    in
    f x x0 x1 x2 x3
  
  (** val coq_CurSystem : coq_Config -> LLVMsyntax.system **)
  
  let coq_CurSystem x = x.coq_CurSystem
  
  (** val coq_CurTargetData : coq_Config -> LLVMtd.coq_TargetData **)
  
  let coq_CurTargetData x = x.coq_CurTargetData
  
  (** val coq_CurProducts : coq_Config -> LLVMsyntax.product list **)
  
  let coq_CurProducts x = x.coq_CurProducts
  
  (** val coq_Globals : coq_Config -> LLVMgv.coq_GVMap **)
  
  let coq_Globals x = x.coq_Globals
  
  (** val coq_FunTable : coq_Config -> LLVMgv.coq_GVMap **)
  
  let coq_FunTable x = x.coq_FunTable
  
  type bConfig = { bCurSystem : LLVMsyntax.system;
                   bCurTargetData : LLVMtd.coq_TargetData;
                   bCurProducts : LLVMsyntax.product list;
                   bGlobals : LLVMgv.coq_GVMap; bFunTable : 
                   LLVMgv.coq_GVMap; bCurFunction : 
                   LLVMsyntax.fdef }
  
  (** val bConfig_rect :
      (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list
      -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.fdef -> 'a1) ->
      bConfig -> 'a1 **)
  
  let bConfig_rect f b =
    let { bCurSystem = x; bCurTargetData = x0; bCurProducts = x1; bGlobals =
      x2; bFunTable = x3; bCurFunction = x4 } = b
    in
    f x x0 x1 x2 x3 x4
  
  (** val bConfig_rec :
      (LLVMsyntax.system -> LLVMtd.coq_TargetData -> LLVMsyntax.product list
      -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.fdef -> 'a1) ->
      bConfig -> 'a1 **)
  
  let bConfig_rec f b =
    let { bCurSystem = x; bCurTargetData = x0; bCurProducts = x1; bGlobals =
      x2; bFunTable = x3; bCurFunction = x4 } = b
    in
    f x x0 x1 x2 x3 x4
  
  (** val bCurSystem : bConfig -> LLVMsyntax.system **)
  
  let bCurSystem x = x.bCurSystem
  
  (** val bCurTargetData : bConfig -> LLVMtd.coq_TargetData **)
  
  let bCurTargetData x = x.bCurTargetData
  
  (** val bCurProducts : bConfig -> LLVMsyntax.product list **)
  
  let bCurProducts x = x.bCurProducts
  
  (** val bGlobals : bConfig -> LLVMgv.coq_GVMap **)
  
  let bGlobals x = x.bGlobals
  
  (** val bFunTable : bConfig -> LLVMgv.coq_GVMap **)
  
  let bFunTable x = x.bFunTable
  
  (** val bCurFunction : bConfig -> LLVMsyntax.fdef **)
  
  let bCurFunction x = x.bCurFunction
 end

module Opsem = 
 struct 
  type coq_GVsMap = (LLVMsyntax.id*coq_GVsT) list
  
  (** val const2GV :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMgv.coq_GVMap ->
      LLVMsyntax.const -> coq_GVsT option **)
  
  let const2GV gVsSig tD gl c =
    match LLVMgv._const2GV tD gl c with
      | Some p -> let gv,ty = p in Some (gVsSig.cgv2gvs gv ty)
      | None -> None
  
  (** val getOperandValue :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.value ->
      coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT option **)
  
  let getOperandValue gVsSig tD v locals globals =
    match v with
      | LLVMsyntax.Coq_value_id id0 -> lookupAL locals id0
      | LLVMsyntax.Coq_value_const c -> const2GV gVsSig tD globals c
  
  type coq_ExecutionContext = { coq_CurFunction : LLVMsyntax.fdef;
                                coq_CurBB : LLVMsyntax.block;
                                coq_CurCmds : LLVMsyntax.cmds;
                                coq_Terminator : LLVMsyntax.terminator;
                                coq_Locals : coq_GVsMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  (** val coq_ExecutionContext_rect :
      coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
      LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock
      list -> 'a1) -> coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rect gVsSig f e =
    let { coq_CurFunction = x; coq_CurBB = x0; coq_CurCmds = x1;
      coq_Terminator = x2; coq_Locals = x3; coq_Allocas = x4 } = e
    in
    f x x0 x1 x2 x3 x4
  
  (** val coq_ExecutionContext_rec :
      coq_GenericValues -> (LLVMsyntax.fdef -> LLVMsyntax.block ->
      LLVMsyntax.cmds -> LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock
      list -> 'a1) -> coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rec gVsSig f e =
    let { coq_CurFunction = x; coq_CurBB = x0; coq_CurCmds = x1;
      coq_Terminator = x2; coq_Locals = x3; coq_Allocas = x4 } = e
    in
    f x x0 x1 x2 x3 x4
  
  (** val coq_CurFunction :
      coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.fdef **)
  
  let coq_CurFunction _ x = x.coq_CurFunction
  
  (** val coq_CurBB :
      coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.block **)
  
  let coq_CurBB _ x = x.coq_CurBB
  
  (** val coq_CurCmds :
      coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.cmds **)
  
  let coq_CurCmds _ x = x.coq_CurCmds
  
  (** val coq_Terminator :
      coq_GenericValues -> coq_ExecutionContext -> LLVMsyntax.terminator **)
  
  let coq_Terminator _ x = x.coq_Terminator
  
  (** val coq_Locals :
      coq_GenericValues -> coq_ExecutionContext -> coq_GVsMap **)
  
  let coq_Locals _ x = x.coq_Locals
  
  (** val coq_Allocas :
      coq_GenericValues -> coq_ExecutionContext -> LLVMgv.mblock list **)
  
  let coq_Allocas _ x = x.coq_Allocas
  
  type coq_ECStack = coq_ExecutionContext list
  
  type coq_State = { coq_ECS : coq_ECStack; coq_Mem : LLVMgv.mem }
  
  (** val coq_State_rect :
      coq_GenericValues -> (coq_ECStack -> LLVMgv.mem -> 'a1) -> coq_State ->
      'a1 **)
  
  let coq_State_rect gVsSig f s =
    let { coq_ECS = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_State_rec :
      coq_GenericValues -> (coq_ECStack -> LLVMgv.mem -> 'a1) -> coq_State ->
      'a1 **)
  
  let coq_State_rec gVsSig f s =
    let { coq_ECS = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_ECS : coq_GenericValues -> coq_State -> coq_ECStack **)
  
  let coq_ECS _ x = x.coq_ECS
  
  (** val coq_Mem : coq_GenericValues -> coq_State -> LLVMgv.mem **)
  
  let coq_Mem _ x = x.coq_Mem
  
  (** val getIncomingValuesForBlockFromPHINodes :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.phinode list
      -> LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap ->
      (LLVMsyntax.id*coq_GVsT) list option **)
  
  let rec getIncomingValuesForBlockFromPHINodes gVsSig tD pNs b globals locals =
    match pNs with
      | [] -> Some []
      | p::pNs0 ->
          let LLVMsyntax.Coq_insn_phi (id0, t, vls) = p in
          (match LLVMinfra.getValueViaBlockFromPHINode
                   (LLVMsyntax.Coq_insn_phi (id0, t, vls)) b with
             | Some v ->
                 (match getOperandValue gVsSig tD v locals globals with
                    | Some gv1 ->
                        (match getIncomingValuesForBlockFromPHINodes gVsSig
                                 tD pNs0 b globals locals with
                           | Some idgvs -> Some ((id0,gv1)::idgvs)
                           | None -> None)
                    | None -> None)
             | None -> None)
  
  (** val updateValuesForNewBlock :
      coq_GenericValues -> (LLVMsyntax.id*coq_GVsT) list -> coq_GVsMap ->
      coq_GVsMap **)
  
  let rec updateValuesForNewBlock gVsSig resultValues locals =
    match resultValues with
      | [] -> locals
      | p::resultValues' ->
          let id0,v = p in
          updateAddAL (updateValuesForNewBlock gVsSig resultValues' locals)
            id0 v
  
  (** val switchToNewBasicBlock :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.block ->
      LLVMsyntax.block -> LLVMgv.coq_GVMap -> coq_GVsMap -> coq_GVsMap option **)
  
  let switchToNewBasicBlock gVsSig tD dest prevBB globals locals =
    let pNs = LLVMinfra.getPHINodesFromBlock dest in
    (match getIncomingValuesForBlockFromPHINodes gVsSig tD pNs prevBB globals
             locals with
       | Some resultValues -> Some
           (updateValuesForNewBlock gVsSig resultValues locals)
       | None -> None)
  
  (** val params2GVs :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.params ->
      coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT list option **)
  
  let rec params2GVs gVsSig tD lp locals globals =
    match lp with
      | [] -> Some []
      | p::lp' ->
          let p0,v = p in
          (match getOperandValue gVsSig tD v locals globals with
             | Some gv ->
                 (match params2GVs gVsSig tD lp' locals globals with
                    | Some gvs -> Some (gv::gvs)
                    | None -> None)
             | None -> None)
  
  (** val exCallUpdateLocals :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool ->
      LLVMsyntax.id -> LLVMgv.coq_GenericValue option -> coq_GVsMap ->
      coq_GVsMap option **)
  
  let exCallUpdateLocals gVsSig tD ft noret rid oResult lc =
    if noret
    then Some lc
    else (match oResult with
            | Some result ->
                (match ft with
                   | LLVMsyntax.Coq_typ_function (t, l, v) ->
                       (match LLVMgv.fit_gv tD t result with
                          | Some gr -> Some
                              (updateAddAL lc rid (gVsSig.gv2gvs gr t))
                          | None -> None)
                   | _ -> None)
            | None -> None)
  
  (** val values2GVs :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.list_sz_value
      -> coq_GVsMap -> LLVMgv.coq_GVMap -> coq_GVsT list option **)
  
  let rec values2GVs gVsSig tD lv locals globals =
    match lv with
      | LLVMsyntax.Nil_list_sz_value -> Some []
      | LLVMsyntax.Cons_list_sz_value (s, v, lv') ->
          (match getOperandValue gVsSig tD v locals globals with
             | Some gV ->
                 (match values2GVs gVsSig tD lv' locals globals with
                    | Some gVs -> Some (gV::gVs)
                    | None -> None)
             | None -> None)
  
  (** val _initializeFrameValues :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
      coq_GVsT list -> coq_GVsMap -> coq_GVsMap option **)
  
  let rec _initializeFrameValues gVsSig tD la lg locals =
    match la with
      | [] -> Some locals
      | p::la' ->
          let p0,id0 = p in
          let t,a = p0 in
          (match lg with
             | [] ->
                 (match _initializeFrameValues gVsSig tD la' [] locals with
                    | Some lc' ->
                        (match LLVMgv.gundef tD t with
                           | Some gv -> Some
                               (updateAddAL lc' id0 (gVsSig.gv2gvs gv t))
                           | None -> None)
                    | None -> None)
             | g::lg' ->
                 (match _initializeFrameValues gVsSig tD la' lg' locals with
                    | Some lc' ->
                        (match gVsSig.lift_op1 (LLVMgv.fit_gv tD t) g t with
                           | Some gv -> Some (updateAddAL lc' id0 gv)
                           | None -> None)
                    | None -> None))
  
  (** val initLocals :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.args ->
      coq_GVsT list -> coq_GVsMap option **)
  
  let initLocals gVsSig tD la lg =
    _initializeFrameValues gVsSig tD la lg []
  
  (** val coq_BOP :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value
      -> LLVMsyntax.value -> coq_GVsT option **)
  
  let coq_BOP gVsSig tD lc gl op bsz v1 v2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 ->
          (match getOperandValue gVsSig tD v2 lc gl with
             | Some gvs2 ->
                 gVsSig.lift_op2 (LLVMgv.mbop tD op bsz) gvs1 gvs2
                   (LLVMsyntax.Coq_typ_int bsz)
             | None -> None)
      | None -> None
  
  (** val coq_FBOP :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.fbop -> LLVMsyntax.floating_point ->
      LLVMsyntax.value -> LLVMsyntax.value -> coq_GVsT option **)
  
  let coq_FBOP gVsSig tD lc gl op fp v1 v2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 ->
          (match getOperandValue gVsSig tD v2 lc gl with
             | Some gvs2 ->
                 gVsSig.lift_op2 (LLVMgv.mfbop tD op fp) gvs1 gvs2
                   (LLVMsyntax.Coq_typ_floatpoint fp)
             | None -> None)
      | None -> None
  
  (** val coq_ICMP :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.cond -> LLVMsyntax.typ ->
      LLVMsyntax.value -> LLVMsyntax.value -> coq_GVsT option **)
  
  let coq_ICMP gVsSig tD lc gl c t v1 v2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 ->
          (match getOperandValue gVsSig tD v2 lc gl with
             | Some gvs2 ->
                 gVsSig.lift_op2 (LLVMgv.micmp tD c t) gvs1 gvs2
                   (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
             | None -> None)
      | None -> None
  
  (** val coq_FCMP :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.fcond -> LLVMsyntax.floating_point ->
      LLVMsyntax.value -> LLVMsyntax.value -> coq_GVsT option **)
  
  let coq_FCMP gVsSig tD lc gl c fp v1 v2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 ->
          (match getOperandValue gVsSig tD v2 lc gl with
             | Some gvs2 ->
                 gVsSig.lift_op2 (LLVMgv.mfcmp tD c fp) gvs1 gvs2
                   (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
             | None -> None)
      | None -> None
  
  (** val coq_CAST :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.castop -> LLVMsyntax.typ ->
      LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option **)
  
  let coq_CAST gVsSig tD lc gl op t1 v1 t2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 -> gVsSig.lift_op1 (LLVMgv.mcast tD op t1 t2) gvs1 t2
      | None -> None
  
  (** val coq_TRUNC :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.truncop -> LLVMsyntax.typ ->
      LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option **)
  
  let coq_TRUNC gVsSig tD lc gl op t1 v1 t2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 -> gVsSig.lift_op1 (LLVMgv.mtrunc tD op t1 t2) gvs1 t2
      | None -> None
  
  (** val coq_EXT :
      coq_GenericValues -> LLVMtd.coq_TargetData -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> LLVMsyntax.extop -> LLVMsyntax.typ ->
      LLVMsyntax.value -> LLVMsyntax.typ -> coq_GVsT option **)
  
  let coq_EXT gVsSig tD lc gl op t1 v1 t2 =
    match getOperandValue gVsSig tD v1 lc gl with
      | Some gvs1 -> gVsSig.lift_op1 (LLVMgv.mext tD op t1 t2) gvs1 t2
      | None -> None
  
  (** val coq_GEP :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
      coq_GVsT -> LLVMgv.coq_GenericValue list -> bool -> coq_GVsT option **)
  
  let coq_GEP gVsSig tD ty mas vidxs inbounds =
    gVsSig.lift_op1 (LLVMgv.gep tD ty vidxs inbounds) mas
      (LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_int
      LLVMsyntax.Size.coq_One))
  
  (** val extractGenericValue :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
      coq_GVsT -> LLVMsyntax.list_const -> coq_GVsT option **)
  
  let extractGenericValue gVsSig tD t gvs cidxs =
    match LLVMinfra.intConsts2Nats tD cidxs with
      | Some idxs ->
          (match LLVMinfra.mgetoffset tD t idxs with
             | Some p ->
                 let o,t' = p in
                 gVsSig.lift_op1 (LLVMgv.mget' tD o t') gvs t'
             | None -> None)
      | None -> None
  
  (** val insertGenericValue :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ ->
      coq_GVsT -> LLVMsyntax.list_const -> LLVMsyntax.typ -> coq_GVsT ->
      coq_GVsT option **)
  
  let insertGenericValue gVsSig tD t gvs cidxs t0 gvs0 =
    match LLVMinfra.intConsts2Nats tD cidxs with
      | Some idxs ->
          (match LLVMinfra.mgetoffset tD t idxs with
             | Some p ->
                 let o,t1 = p in
                 gVsSig.lift_op2 (LLVMgv.mset' tD o t t0) gvs gvs0 t
             | None -> None)
      | None -> None
  
  (** val returnUpdateLocals :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.cmd ->
      LLVMsyntax.value -> coq_GVsMap -> coq_GVsMap -> LLVMgv.coq_GVMap ->
      coq_GVsMap option **)
  
  let returnUpdateLocals gVsSig tD c' result lc lc' gl =
    match getOperandValue gVsSig tD result lc gl with
      | Some gr ->
          (match c' with
             | LLVMsyntax.Coq_insn_call (id0, n, c, t, v, p) ->
                 if n
                 then Some lc'
                 else (match t with
                         | LLVMsyntax.Coq_typ_function (
                             ct, l, v0) ->
                             (match gVsSig.lift_op1 
                                      (LLVMgv.fit_gv tD ct) gr ct with
                                | Some gr' -> Some (updateAddAL lc' id0 gr')
                                | None -> None)
                         | _ -> None)
             | _ -> None)
      | None -> None
  
  (** val s_genInitState :
      coq_GenericValues -> LLVMsyntax.system -> LLVMsyntax.id -> coq_GVsT
      list -> LLVMgv.mem -> (OpsemAux.coq_Config*coq_State) option **)
  
  let s_genInitState gVsSig s main args0 initmem =
    match LLVMinfra.lookupFdefViaIDFromSystem s main with
      | Some curFunction ->
          (match LLVMinfra.getParentOfFdefFromSystem curFunction s with
             | Some m ->
                 let LLVMsyntax.Coq_module_intro
                   (curLayouts, curNamedts, curProducts) = m
                 in
                 let initargetdata =
                   OpsemAux.initTargetData curLayouts curNamedts initmem
                 in
                 (match OpsemAux.genGlobalAndInitMem initargetdata
                          curProducts [] [] initmem with
                    | Some p ->
                        let p0,initMem = p in
                        let initGlobal0,initFunTable0 = p0 in
                        (match LLVMinfra.getEntryBlock curFunction with
                           | Some b ->
                               let LLVMsyntax.Coq_block_intro
                                 (l, ps, cs, tmn) = b
                               in
                               let LLVMsyntax.Coq_fdef_intro (
                                 f, b0) = curFunction
                               in
                               let LLVMsyntax.Coq_fheader_intro
                                 (f0, rt, i, la, v) = f
                               in
                               (match initLocals gVsSig initargetdata la
                                        args0 with
                                  | Some values -> Some
                                      ({ OpsemAux.coq_CurSystem = s;
                                      OpsemAux.coq_CurTargetData =
                                      initargetdata;
                                      OpsemAux.coq_CurProducts = curProducts;
                                      OpsemAux.coq_Globals = initGlobal0;
                                      OpsemAux.coq_FunTable =
                                      initFunTable0 },{ coq_ECS =
                                      ({ coq_CurFunction = curFunction;
                                      coq_CurBB = (LLVMsyntax.Coq_block_intro
                                      (l, ps, cs, tmn)); coq_CurCmds = cs;
                                      coq_Terminator = tmn; coq_Locals =
                                      values; coq_Allocas = [] }::[]);
                                      coq_Mem = initMem })
                                  | None -> None)
                           | None -> None)
                    | None -> None)
             | None -> None)
      | None -> None
  
  (** val s_isFinialState : coq_GenericValues -> coq_State -> bool **)
  
  let s_isFinialState gVsSig state =
    let { coq_ECS = eCS; coq_Mem = mem0 } = state in
    (match eCS with
       | [] -> false
       | e::l ->
           let { coq_CurFunction = curFunction; coq_CurBB = curBB;
             coq_CurCmds = curCmds; coq_Terminator = terminator0;
             coq_Locals = locals; coq_Allocas = allocas } = e
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
  
  (** val callUpdateLocals :
      coq_GenericValues -> LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool ->
      LLVMsyntax.id -> LLVMsyntax.value option -> coq_GVsMap -> coq_GVsMap ->
      LLVMgv.coq_GVMap -> coq_GVsMap option **)
  
  let callUpdateLocals gVsSig tD ft noret rid oResult lc lc' gl =
    if noret
    then (match oResult with
            | Some result ->
                (match getOperandValue gVsSig tD result lc' gl with
                   | Some gr -> Some lc
                   | None -> None)
            | None -> Some lc)
    else (match oResult with
            | Some result ->
                (match getOperandValue gVsSig tD result lc' gl with
                   | Some gr ->
                       (match ft with
                          | LLVMsyntax.Coq_typ_function (
                              t, l, v) ->
                              (match gVsSig.lift_op1 
                                       (LLVMgv.fit_gv tD t) gr t with
                                 | Some gr' -> Some (updateAddAL lc rid gr')
                                 | None -> None)
                          | _ -> None)
                   | None -> None)
            | None -> None)
  
  type bExecutionContext = { bCurBB : LLVMsyntax.block;
                             bCurCmds : LLVMsyntax.cmds;
                             bTerminator : LLVMsyntax.terminator;
                             bLocals : coq_GVsMap;
                             bAllocas : LLVMgv.mblock list; bMem : 
                             LLVMgv.mem }
  
  (** val bExecutionContext_rect :
      coq_GenericValues -> (LLVMsyntax.block -> LLVMsyntax.cmds ->
      LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock list -> LLVMgv.mem
      -> 'a1) -> bExecutionContext -> 'a1 **)
  
  let bExecutionContext_rect gVsSig f b =
    let { bCurBB = x; bCurCmds = x0; bTerminator = x1; bLocals = x2;
      bAllocas = x3; bMem = x4 } = b
    in
    f x x0 x1 x2 x3 x4
  
  (** val bExecutionContext_rec :
      coq_GenericValues -> (LLVMsyntax.block -> LLVMsyntax.cmds ->
      LLVMsyntax.terminator -> coq_GVsMap -> LLVMgv.mblock list -> LLVMgv.mem
      -> 'a1) -> bExecutionContext -> 'a1 **)
  
  let bExecutionContext_rec gVsSig f b =
    let { bCurBB = x; bCurCmds = x0; bTerminator = x1; bLocals = x2;
      bAllocas = x3; bMem = x4 } = b
    in
    f x x0 x1 x2 x3 x4
  
  (** val bCurBB :
      coq_GenericValues -> bExecutionContext -> LLVMsyntax.block **)
  
  let bCurBB _ x = x.bCurBB
  
  (** val bCurCmds :
      coq_GenericValues -> bExecutionContext -> LLVMsyntax.cmds **)
  
  let bCurCmds _ x = x.bCurCmds
  
  (** val bTerminator :
      coq_GenericValues -> bExecutionContext -> LLVMsyntax.terminator **)
  
  let bTerminator _ x = x.bTerminator
  
  (** val bLocals : coq_GenericValues -> bExecutionContext -> coq_GVsMap **)
  
  let bLocals _ x = x.bLocals
  
  (** val bAllocas :
      coq_GenericValues -> bExecutionContext -> LLVMgv.mblock list **)
  
  let bAllocas _ x = x.bAllocas
  
  (** val bMem : coq_GenericValues -> bExecutionContext -> LLVMgv.mem **)
  
  let bMem _ x = x.bMem
  
  (** val b_genInitState :
      coq_GenericValues -> LLVMsyntax.system -> LLVMsyntax.id -> coq_GVsT
      list -> LLVMgv.mem -> (OpsemAux.bConfig*bExecutionContext) option **)
  
  let b_genInitState gVsSig s main args0 initmem =
    match s_genInitState gVsSig s main args0 initmem with
      | Some p ->
          let c,s0 = p in
          let { OpsemAux.coq_CurSystem = s1; OpsemAux.coq_CurTargetData = tD;
            OpsemAux.coq_CurProducts = ps; OpsemAux.coq_Globals = gl;
            OpsemAux.coq_FunTable = fs } = c
          in
          let { coq_ECS = eCS; coq_Mem = m } = s0 in
          (match eCS with
             | [] -> None
             | e::l ->
                 let { coq_CurFunction = f; coq_CurBB = b; coq_CurCmds = cs;
                   coq_Terminator = tmn; coq_Locals = lc; coq_Allocas =
                   als } = e
                 in
                 (match l with
                    | [] -> Some ({ OpsemAux.bCurSystem = s1;
                        OpsemAux.bCurTargetData = tD; OpsemAux.bCurProducts =
                        ps; OpsemAux.bGlobals = gl; OpsemAux.bFunTable = fs;
                        OpsemAux.bCurFunction = f },{ bCurBB = b; bCurCmds =
                        cs; bTerminator = tmn; bLocals = lc; bAllocas = als;
                        bMem = m })
                    | e0::l0 -> None))
      | None -> None
  
  (** val b_isFinialState :
      coq_GenericValues -> bExecutionContext -> bool **)
  
  let b_isFinialState gVsSig ec =
    let { bCurBB = bCurBB0; bCurCmds = bCurCmds0; bTerminator = bTerminator0;
      bLocals = bLocals0; bAllocas = bAllocas0; bMem = bMem0 } = ec
    in
    (match bCurCmds0 with
       | [] ->
           (match bTerminator0 with
              | LLVMsyntax.Coq_insn_return (i, t, v) -> true
              | LLVMsyntax.Coq_insn_return_void i -> true
              | _ -> false)
       | c::l -> false)
 end

