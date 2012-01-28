open BinInt
open BinPos
open CoqEqDec
open Coqlib
open Datatypes
open List0
open Metatheory
open MetatheoryAtom
open Alist
open Genericvalues
open Infrastructure
open Monad
open Sub_symexe
open Syntax
open Targetdata

val eq_value : LLVMsyntax.value -> LLVMsyntax.value -> bool

val tv_typ : LLVMsyntax.typ -> LLVMsyntax.typ -> bool

val tv_align : LLVMsyntax.align -> LLVMsyntax.align -> bool

val eq_sterm : SBSE.sterm -> SBSE.sterm -> bool

val eq_smem : SBSE.smem -> SBSE.smem -> bool

val eq_id : LLVMsyntax.id -> LLVMsyntax.id -> bool

val eq_const : LLVMsyntax.const -> LLVMsyntax.const -> bool

val eq_l : LLVMsyntax.l -> LLVMsyntax.l -> bool

val bzeq : coq_Z -> coq_Z -> bool

val eq_INT_Z : LLVMsyntax.coq_Int -> coq_Z -> bool

module SBsyntax : 
 sig 
  type call =
    | Coq_insn_call_nptr of LLVMsyntax.id * LLVMsyntax.noret
       * LLVMsyntax.clattrs * LLVMsyntax.typ * LLVMsyntax.value
       * LLVMsyntax.params
    | Coq_insn_call_ptr of LLVMsyntax.id * LLVMsyntax.noret
       * LLVMsyntax.clattrs * LLVMsyntax.typ * LLVMsyntax.value
       * LLVMsyntax.params * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.const * 
       LLVMsyntax.const * LLVMsyntax.const
  
  val call_rect :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) ->
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> LLVMsyntax.id
    -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.const -> 'a1) -> call -> 'a1
  
  val call_rec :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) ->
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> LLVMsyntax.id
    -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.const -> 'a1) -> call -> 'a1
  
  val sz32 : LLVMsyntax.Size.t
  
  val i32 : LLVMsyntax.typ
  
  val i8 : LLVMsyntax.typ
  
  val p32 : LLVMsyntax.typ
  
  val p8 : LLVMsyntax.typ
  
  val pp32 : LLVMsyntax.typ
  
  val pp8 : LLVMsyntax.typ
  
  val cpars :
    LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.list_sz_value
  
  val call_ptr :
    LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs -> LLVMsyntax.typ
    -> LLVMsyntax.value -> ((LLVMsyntax.typ*LLVMsyntax.attribute
    list)*LLVMsyntax.value) list -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const
    -> call*LLVMsyntax.cmd list
  
  type subblock = { coq_NBs : SBSE.nbranch list; call_cmd : call }
  
  val subblock_rect : (SBSE.nbranch list -> call -> 'a1) -> subblock -> 'a1
  
  val subblock_rec : (SBSE.nbranch list -> call -> 'a1) -> subblock -> 'a1
  
  val coq_NBs : subblock -> SBSE.nbranch list
  
  val call_cmd : subblock -> call
  
  type iterminator =
    | Coq_insn_return_ptr of LLVMsyntax.id * LLVMsyntax.typ * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.value * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.value * LLVMsyntax.id * LLVMsyntax.value * 
       LLVMsyntax.id * LLVMsyntax.const * LLVMsyntax.const * 
       LLVMsyntax.const
  
  val iterminator_rect :
    (LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id ->
    LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const -> 'a1) ->
    iterminator -> 'a1
  
  val iterminator_rec :
    (LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id ->
    LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const -> 'a1) ->
    iterminator -> 'a1
  
  val ret_ptr :
    LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id ->
    LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.cmd list*LLVMsyntax.terminator
  
  type block =
    | Coq_block_common of LLVMsyntax.l * LLVMsyntax.phinodes * 
       subblock list * SBSE.nbranch list * LLVMsyntax.terminator
    | Coq_block_ret_ptr of LLVMsyntax.l * LLVMsyntax.phinodes * 
       subblock list * SBSE.nbranch list * iterminator
  
  val block_rect :
    (LLVMsyntax.l -> LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch
    list -> LLVMsyntax.terminator -> 'a1) -> (LLVMsyntax.l ->
    LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch list -> iterminator
    -> 'a1) -> block -> 'a1
  
  val block_rec :
    (LLVMsyntax.l -> LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch
    list -> LLVMsyntax.terminator -> 'a1) -> (LLVMsyntax.l ->
    LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch list -> iterminator
    -> 'a1) -> block -> 'a1
  
  type blocks = block list
  
  type fdef =
    | Coq_fdef_intro of LLVMsyntax.fheader * blocks
  
  val fdef_rect : (LLVMsyntax.fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  val fdef_rec : (LLVMsyntax.fheader -> blocks -> 'a1) -> fdef -> 'a1
  
  type product =
    | Coq_product_gvar of LLVMsyntax.gvar
    | Coq_product_fdec of LLVMsyntax.fdec
    | Coq_product_fdef of fdef
  
  val product_rect :
    (LLVMsyntax.gvar -> 'a1) -> (LLVMsyntax.fdec -> 'a1) -> (fdef -> 'a1) ->
    product -> 'a1
  
  val product_rec :
    (LLVMsyntax.gvar -> 'a1) -> (LLVMsyntax.fdec -> 'a1) -> (fdef -> 'a1) ->
    product -> 'a1
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of LLVMsyntax.layouts * LLVMsyntax.namedts * products
  
  val module_rect :
    (LLVMsyntax.layouts -> LLVMsyntax.namedts -> products -> 'a1) ->
    coq_module -> 'a1
  
  val module_rec :
    (LLVMsyntax.layouts -> LLVMsyntax.namedts -> products -> 'a1) ->
    coq_module -> 'a1
  
  type modules = coq_module list
  
  type system = modules
  
  val isCall_inv :
    LLVMsyntax.cmd ->
    ((((LLVMsyntax.id*LLVMsyntax.noret)*LLVMsyntax.clattrs)*LLVMsyntax.typ)*LLVMsyntax.value)*LLVMsyntax.params
  
  val get_named_ret_typs :
    LLVMsyntax.namedt list -> LLVMsyntax.id ->
    ((LLVMsyntax.typ*LLVMsyntax.typ)*LLVMsyntax.typ) option
  
  val get_ret_typs :
    LLVMsyntax.namedt list -> LLVMsyntax.typ ->
    ((LLVMsyntax.typ*LLVMsyntax.typ)*LLVMsyntax.typ) option
  
  val gen_icall :
    LLVMsyntax.namedt list ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.value) list ->
    LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd ->
    LLVMsyntax.cmd -> LLVMsyntax.cmd ->
    (((((((((((LLVMsyntax.params*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.typ)
    option
  
  val of_llvm_cmds :
    LLVMsyntax.namedts -> LLVMsyntax.cmds -> subblock list*SBSE.nbranch list
  
  val gen_iret :
    LLVMsyntax.namedt list -> LLVMsyntax.typ -> LLVMsyntax.id ->
    LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd ->
    LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.id ->
    ((((((((((((((LLVMsyntax.id*LLVMsyntax.typ)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.const)
    option
  
  val get_last_six_insns :
    LLVMsyntax.cmds ->
    LLVMsyntax.cmds*(((((LLVMsyntax.cmd*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)
    option
  
  val of_llvm_block :
    (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.fheader ->
    LLVMsyntax.block -> block
  
  val of_llvm_fdef :
    (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.fdef -> fdef
  
  val of_llvm_products :
    (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.products ->
    products
  
  val of_llvm_module : LLVMsyntax.coq_module -> coq_module
  
  val of_llvm_system : LLVMsyntax.system -> system
  
  val call_to_llvm_cmds : call -> LLVMsyntax.cmds
  
  val subblock_to_llvm_cmds : subblock -> LLVMsyntax.cmds
  
  val ret_ptr_to_tmn :
    LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id ->
    LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.cmd list*LLVMsyntax.terminator
  
  val itmn_to_llvm_tmn : iterminator -> LLVMsyntax.cmds*LLVMsyntax.terminator
  
  val to_llvm_block : block -> LLVMsyntax.block
  
  val to_llvm_fdef : fdef -> LLVMsyntax.fdef
  
  val to_llvm_product : product -> LLVMsyntax.product
  
  val to_llvm_products : products -> LLVMsyntax.products
  
  val to_llvm_module : coq_module -> LLVMsyntax.coq_module
  
  val to_llvm_system : system -> LLVMsyntax.system
  
  val getFheader : fdef -> LLVMsyntax.fheader
  
  type l2block = (LLVMsyntax.l*block) list
  
  val genLabel2Block_block : block -> l2block
  
  val genLabel2Block_blocks : blocks -> l2block
  
  val genLabel2Block_fdef : fdef -> l2block
  
  val lookupBlockViaLabelFromFdef : fdef -> LLVMsyntax.l -> block option
  
  val getPHINodesFromBlock : block -> LLVMsyntax.phinode list
  
  val getValueViaBlockFromValuels :
    LLVMsyntax.list_value_l -> block -> LLVMsyntax.value option
  
  val getValueViaBlockFromPHINode :
    LLVMsyntax.phinode -> block -> LLVMsyntax.value option
  
  val getIncomingValuesForBlockFromPHINodes :
    LLVMtd.coq_TargetData -> LLVMsyntax.phinode list -> block ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap ->
    (LLVMsyntax.id*LLVMgv.coq_GenericValue) list option
  
  val updateValuesForNewBlock :
    (LLVMsyntax.id*LLVMgv.coq_GenericValue) list -> LLVMgv.coq_GVMap ->
    LLVMgv.coq_GVMap
  
  val switchToNewBasicBlock :
    LLVMtd.coq_TargetData -> block -> block -> LLVMgv.coq_GVMap ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap option
  
  val lookupFdecViaIDFromProduct :
    product -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromProducts :
    products -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val getFdefID : fdef -> LLVMsyntax.id
  
  val lookupFdefViaIDFromProduct : product -> LLVMsyntax.id -> fdef option
  
  val lookupFdefViaIDFromProducts : products -> LLVMsyntax.id -> fdef option
  
  val lookupFdefViaGVFromFunTable :
    LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue -> LLVMsyntax.id option
  
  val lookupExFdecViaGV :
    LLVMtd.coq_TargetData -> products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap
    -> LLVMgv.coq_GVMap -> LLVMsyntax.value -> LLVMsyntax.fdec option
  
  val lookupFdefViaGV :
    LLVMtd.coq_TargetData -> products -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap
    -> LLVMgv.coq_GVMap -> LLVMsyntax.value -> fdef option
  
  val getEntryBlock : fdef -> block option
  
  val lookupGvarViaIDFromProducts :
    products -> LLVMsyntax.id -> LLVMsyntax.gvar option
  
  val lookupGvarFromProduct :
    product -> LLVMsyntax.id -> LLVMsyntax.gvar option
  
  val lookupGvarFromProducts :
    products -> LLVMsyntax.id -> LLVMsyntax.gvar option
  
  val lookupFdecFromProducts :
    products -> LLVMsyntax.id -> LLVMsyntax.fdec option
 end

module SBopsem : 
 sig 
  val exCallUpdateLocals :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool -> LLVMsyntax.id ->
    LLVMgv.coq_GenericValue option -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap
    option
  
  type coq_ExecutionContext = { coq_CurBB : SBsyntax.block;
                                coq_Locals : LLVMgv.coq_GVMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  val coq_ExecutionContext_rect :
    (SBsyntax.block -> LLVMgv.coq_GVMap -> LLVMgv.mblock list -> 'a1) ->
    coq_ExecutionContext -> 'a1
  
  val coq_ExecutionContext_rec :
    (SBsyntax.block -> LLVMgv.coq_GVMap -> LLVMgv.mblock list -> 'a1) ->
    coq_ExecutionContext -> 'a1
  
  val coq_CurBB : coq_ExecutionContext -> SBsyntax.block
  
  val coq_Locals : coq_ExecutionContext -> LLVMgv.coq_GVMap
  
  val coq_Allocas : coq_ExecutionContext -> LLVMgv.mblock list
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : LLVMgv.mem }
  
  val coq_State_rect :
    (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1
  
  val coq_State_rec :
    (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1
  
  val coq_Frame : coq_State -> coq_ExecutionContext
  
  val coq_Mem : coq_State -> LLVMgv.mem
  
  val callUpdateLocals :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool -> LLVMsyntax.id ->
    LLVMsyntax.value option -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap ->
    LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap option
 end

