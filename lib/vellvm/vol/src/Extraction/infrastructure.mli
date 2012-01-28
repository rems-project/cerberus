open AST
open BinInt
open Bool
open CoqEqDec
open Datatypes
open List0
open ListSet
open MetatheoryAtom
open Peano
open Alist
open Monad
open Syntax
open Targetdata

type __ = Obj.t

module LLVMinfra : 
 sig 
  val id_dec : LLVMsyntax.id -> LLVMsyntax.id -> bool
  
  val l_dec : LLVMsyntax.l -> LLVMsyntax.l -> bool
  
  val inbounds_dec : LLVMsyntax.inbounds -> LLVMsyntax.inbounds -> bool
  
  val tailc_dec : LLVMsyntax.tailc -> LLVMsyntax.tailc -> bool
  
  val varg_dec : LLVMsyntax.varg -> LLVMsyntax.varg -> bool
  
  val noret_dec : LLVMsyntax.noret -> LLVMsyntax.noret -> bool
  
  val lempty_set : LLVMsyntax.l set
  
  val lset_add : LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_union : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_inter : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set
  
  val lset_eqb : LLVMsyntax.ls -> LLVMsyntax.ls -> bool
  
  val lset_neqb : LLVMsyntax.ls -> LLVMsyntax.ls -> bool
  
  val lset_single : LLVMsyntax.l -> LLVMsyntax.l set
  
  val lset_mem : LLVMsyntax.l -> LLVMsyntax.ls -> bool
  
  val getCmdLoc : LLVMsyntax.cmd -> LLVMsyntax.id
  
  val getTerminatorID : LLVMsyntax.terminator -> LLVMsyntax.id
  
  val getPhiNodeID : LLVMsyntax.phinode -> LLVMsyntax.id
  
  val getValueID : LLVMsyntax.value -> LLVMsyntax.id option
  
  val getInsnLoc : LLVMsyntax.insn -> LLVMsyntax.id
  
  val isPhiNodeB : LLVMsyntax.insn -> bool
  
  val getCmdID : LLVMsyntax.cmd -> LLVMsyntax.id option
  
  val getCmdsIDs : LLVMsyntax.cmds -> AtomImpl.atom list
  
  val getPhiNodesIDs : LLVMsyntax.phinodes -> AtomImpl.atom list
  
  val getBlockIDs : LLVMsyntax.block -> AtomImpl.atom list
  
  val getArgsIDs : LLVMsyntax.args -> AtomImpl.atom list
  
  val getInsnID : LLVMsyntax.insn -> LLVMsyntax.id option
  
  val mgetoffset_aux :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_Z list -> coq_Z ->
    (coq_Z*LLVMsyntax.typ) option
  
  val mgetoffset :
    LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_Z list ->
    (coq_Z*LLVMsyntax.typ) option
  
  val intConsts2Nats :
    LLVMtd.coq_TargetData -> LLVMsyntax.list_const -> coq_Z list option
  
  val getSubTypFromConstIdxs :
    LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getConstGEPTyp :
    LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getSubTypFromValueIdxs :
    LLVMsyntax.list_sz_value -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getGEPTyp :
    LLVMsyntax.list_sz_value -> LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getCmdTyp : LLVMsyntax.cmd -> LLVMsyntax.typ option
  
  val getTerminatorTyp : LLVMsyntax.terminator -> LLVMsyntax.typ
  
  val getPhiNodeTyp : LLVMsyntax.phinode -> LLVMsyntax.typ
  
  val getInsnTyp : LLVMsyntax.insn -> LLVMsyntax.typ option
  
  val getPointerEltTyp : LLVMsyntax.typ -> LLVMsyntax.typ option
  
  val getValueIDs : LLVMsyntax.value -> LLVMsyntax.ids
  
  val values2ids : LLVMsyntax.value list -> LLVMsyntax.ids
  
  val getParamsOperand : LLVMsyntax.params -> LLVMsyntax.ids
  
  val list_prj1 : ('a1*'a2) list -> 'a1 list
  
  val list_prj2 : ('a1*'a2) list -> 'a2 list
  
  val getCmdOperands : LLVMsyntax.cmd -> LLVMsyntax.ids
  
  val getTerminatorOperands : LLVMsyntax.terminator -> LLVMsyntax.ids
  
  val getPhiNodeOperands : LLVMsyntax.phinode -> LLVMsyntax.ids
  
  val getInsnOperands : LLVMsyntax.insn -> LLVMsyntax.ids
  
  val getCmdLabels : LLVMsyntax.cmd -> LLVMsyntax.ls
  
  val getTerminatorLabels : LLVMsyntax.terminator -> LLVMsyntax.ls
  
  val getPhiNodeLabels : LLVMsyntax.phinode -> LLVMsyntax.ls
  
  val getInsnLabels : LLVMsyntax.insn -> LLVMsyntax.ls
  
  val args2Typs : LLVMsyntax.args -> LLVMsyntax.list_typ
  
  val getFheaderTyp : LLVMsyntax.fheader -> LLVMsyntax.typ
  
  val getFdecTyp : LLVMsyntax.fdec -> LLVMsyntax.typ
  
  val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
  
  val getBindingTyp : LLVMsyntax.id_binding -> LLVMsyntax.typ option
  
  val getCmdsFromBlock : LLVMsyntax.block -> LLVMsyntax.cmds
  
  val getPhiNodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinodes
  
  val getTerminatorFromBlock : LLVMsyntax.block -> LLVMsyntax.terminator
  
  val getFheaderID : LLVMsyntax.fheader -> LLVMsyntax.id
  
  val getFdecID : LLVMsyntax.fdec -> LLVMsyntax.id
  
  val getFdefID : LLVMsyntax.fdef -> LLVMsyntax.id
  
  val getLabelViaIDFromList :
    LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelViaIDFromPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelsFromIdls : LLVMsyntax.list_value_l -> LLVMsyntax.ls
  
  val getLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.ls
  
  val getLabelsFromPhiNodes : LLVMsyntax.phinode list -> LLVMsyntax.ls
  
  val getIDLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.list_value_l
  
  val getLabelViaIDFromIDLabels :
    LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val _getLabelViaIDPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getLabelViaIDPhiNode :
    LLVMsyntax.insn -> LLVMsyntax.id -> LLVMsyntax.l option
  
  val getReturnTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
  
  val getGvarID : LLVMsyntax.gvar -> LLVMsyntax.id
  
  val getCalledValue : LLVMsyntax.insn -> LLVMsyntax.value option
  
  val getCalledValueID : LLVMsyntax.insn -> LLVMsyntax.id option
  
  val getCallerReturnID : LLVMsyntax.cmd -> LLVMsyntax.id option
  
  val getValueViaLabelFromValuels :
    LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.value option
  
  val getValueViaBlockFromValuels :
    LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.value option
  
  val getValueViaBlockFromPHINode :
    LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.value option
  
  val getPHINodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinode list
  
  val getEntryBlock : LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getEntryCmds : LLVMsyntax.block -> LLVMsyntax.cmds
  
  val floating_point_order :
    LLVMsyntax.floating_point -> LLVMsyntax.floating_point -> bool
  
  val wf_fcond : LLVMsyntax.fcond -> bool
  
  val lookupCmdViaIDFromCmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmd option
  
  val lookupPhiNodeViaIDFromPhiNodes :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.phinode option
  
  val lookupInsnViaIDFromBlock :
    LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.insn option
  
  val lookupInsnViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.insn option
  
  val lookupInsnViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.insn option
  
  val lookupArgViaIDFromArgs :
    LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.arg option
  
  val lookupBlockViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.block option
  
  val lookupBlockViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.block option
  
  val lookupFdecViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdecViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdec option
  
  val lookupFdefViaIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupFdefViaIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdef option
  
  val lookupTypViaIDFromCmd :
    LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromCmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromPhiNode :
    LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromPhiNodes :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromTerminator :
    LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromBlock :
    LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromArgs :
    LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaIDFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaGIDFromProduct :
    LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaGIDFromProducts :
    LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaGIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaGIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaGIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaTIDFromNamedts :
    LLVMsyntax.namedts -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaTIDFromModule :
    LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaTIDFromModules :
    LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  val lookupTypViaTIDFromSystem :
    LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option
  
  type l2block = (LLVMsyntax.l*LLVMsyntax.block) list
  
  val genLabel2Block_block : LLVMsyntax.block -> l2block
  
  val genLabel2Block_blocks : LLVMsyntax.blocks -> l2block
  
  val genLabel2Block_fdef : LLVMsyntax.fdef -> l2block
  
  val genLabel2Block_product : LLVMsyntax.product -> l2block
  
  val genLabel2Block_products : LLVMsyntax.products -> l2block
  
  val genLabel2Block : LLVMsyntax.coq_module -> l2block
  
  val getNonEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.blocks
  
  val lookupBlockViaLabelFromBlocks :
    LLVMsyntax.blocks -> LLVMsyntax.l -> LLVMsyntax.block option
  
  val lookupBlockViaLabelFromFdef :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block option
  
  val getLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls
  
  val update_udb :
    LLVMsyntax.usedef_block -> LLVMsyntax.l -> LLVMsyntax.l ->
    LLVMsyntax.usedef_block
  
  val genBlockUseDef_block :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.usedef_block
  
  val genBlockUseDef_blocks :
    LLVMsyntax.block list -> LLVMsyntax.usedef_block ->
    LLVMsyntax.usedef_block
  
  val genBlockUseDef_fdef : LLVMsyntax.fdef -> LLVMsyntax.usedef_block
  
  val getBlockLabel : LLVMsyntax.block -> LLVMsyntax.l
  
  val getBlockUseDef :
    LLVMsyntax.usedef_block -> LLVMsyntax.block -> LLVMsyntax.l list option
  
  val getTerminator : LLVMsyntax.block -> LLVMsyntax.terminator
  
  val getLabelsFromSwitchCases :
    (LLVMsyntax.const*LLVMsyntax.l) list -> LLVMsyntax.ls
  
  val getLabelsFromTerminator : LLVMsyntax.terminator -> LLVMsyntax.ls
  
  val getBlocksFromLabels : LLVMsyntax.ls -> l2block -> LLVMsyntax.blocks
  
  val succOfBlock :
    LLVMsyntax.block -> LLVMsyntax.coq_module -> LLVMsyntax.blocks
  
  val predOfBlock :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.l list
  
  val hasSinglePredecessor :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool
  
  val hasNonePredecessor :
    LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool
  
  val successors_terminator : LLVMsyntax.terminator -> LLVMsyntax.ls
  
  val isPointerTypB : LLVMsyntax.typ -> bool
  
  val isFunctionPointerTypB : LLVMsyntax.typ -> bool
  
  val isArrayTypB : LLVMsyntax.typ -> bool
  
  val isReturnInsnB : LLVMsyntax.terminator -> bool
  
  val _isCallInsnB : LLVMsyntax.cmd -> bool
  
  val isCallInsnB : LLVMsyntax.insn -> bool
  
  val isNotValidReturnTypB : LLVMsyntax.typ -> bool
  
  val isValidReturnTypB : LLVMsyntax.typ -> bool
  
  val isNotFirstClassTypB : LLVMsyntax.typ -> bool
  
  val isFirstClassTypB : LLVMsyntax.typ -> bool
  
  val isValidArgumentTypB : LLVMsyntax.typ -> bool
  
  val isNotValidElementTypB : LLVMsyntax.typ -> bool
  
  val isValidElementTypB : LLVMsyntax.typ -> bool
  
  val isBindingFdecB : LLVMsyntax.id_binding -> bool
  
  val isBindingGvarB : LLVMsyntax.id_binding -> bool
  
  val isBindingArgB : LLVMsyntax.id_binding -> bool
  
  val isBindingCmdB : LLVMsyntax.id_binding -> bool
  
  val isBindingTerminatorB : LLVMsyntax.id_binding -> bool
  
  val isBindingPhiNodeB : LLVMsyntax.id_binding -> bool
  
  val isBindingInsnB : LLVMsyntax.id_binding -> bool
  
  val isBindingFdec : LLVMsyntax.id_binding -> LLVMsyntax.fdec option
  
  val isBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option
  
  val isBindingGvar : LLVMsyntax.id_binding -> LLVMsyntax.gvar option
  
  val isBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option
  
  val isBindingPhiNode : LLVMsyntax.id_binding -> LLVMsyntax.phinode option
  
  val isBindingTerminator :
    LLVMsyntax.id_binding -> LLVMsyntax.terminator option
  
  val isBindingInsn : LLVMsyntax.id_binding -> LLVMsyntax.insn option
  
  val getCmdsLocs : LLVMsyntax.cmd list -> LLVMsyntax.ids
  
  val getBlockLocs : LLVMsyntax.block -> LLVMsyntax.ids
  
  val getBlocksLocs : LLVMsyntax.block list -> LLVMsyntax.ids
  
  val getBlocksLabels : LLVMsyntax.block list -> LLVMsyntax.ls
  
  val getProductID : LLVMsyntax.product -> LLVMsyntax.id
  
  val getProductsIDs : LLVMsyntax.product list -> LLVMsyntax.ids
  
  val getNamedtsIDs : LLVMsyntax.namedt list -> LLVMsyntax.ids
  
  val sumbool2bool : bool -> bool
  
  val floating_point_dec :
    LLVMsyntax.floating_point -> LLVMsyntax.floating_point -> bool
  
  type typ_dec_prop = LLVMsyntax.typ -> bool
  
  type list_typ_dec_prop = LLVMsyntax.list_typ -> bool
  
  val typ_mutrec_dec :
    (LLVMsyntax.typ -> typ_dec_prop)*(LLVMsyntax.list_typ ->
    list_typ_dec_prop)
  
  val typ_dec : LLVMsyntax.typ -> LLVMsyntax.typ -> bool
  
  val list_typ_dec : LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool
  
  val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> bool
  
  val fbop_dec : LLVMsyntax.fbop -> LLVMsyntax.fbop -> bool
  
  val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> bool
  
  val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> bool
  
  val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> bool
  
  val fcond_dec : LLVMsyntax.fcond -> LLVMsyntax.fcond -> bool
  
  val truncop_dec : LLVMsyntax.truncop -> LLVMsyntax.truncop -> bool
  
  type const_dec_prop = LLVMsyntax.const -> bool
  
  type list_const_dec_prop = LLVMsyntax.list_const -> bool
  
  val const_mutrec_dec :
    (LLVMsyntax.const -> const_dec_prop)*(LLVMsyntax.list_const ->
    list_const_dec_prop)
  
  val const_dec : LLVMsyntax.const -> LLVMsyntax.const -> bool
  
  val list_const_dec : LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool
  
  val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> bool
  
  val attribute_dec : LLVMsyntax.attribute -> LLVMsyntax.attribute -> bool
  
  val attributes_dec : LLVMsyntax.attributes -> LLVMsyntax.attributes -> bool
  
  val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> bool
  
  val list_value_l_dec :
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool
  
  val list_value_dec :
    LLVMsyntax.list_sz_value -> LLVMsyntax.list_sz_value -> bool
  
  val callconv_dec : LLVMsyntax.callconv -> LLVMsyntax.callconv -> bool
  
  val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool
  
  val terminator_dec : LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool
  
  val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool
  
  val insn_dec : LLVMsyntax.insn -> LLVMsyntax.insn -> bool
  
  val cmds_dec : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool
  
  val phinodes_dec :
    LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool
  
  val block_dec : LLVMsyntax.block -> LLVMsyntax.block -> bool
  
  val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> bool
  
  val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> bool
  
  val visibility_dec : LLVMsyntax.visibility -> LLVMsyntax.visibility -> bool
  
  val linkage_dec : LLVMsyntax.linkage -> LLVMsyntax.linkage -> bool
  
  val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool
  
  val blocks_dec : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool
  
  val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool
  
  val fdef_dec : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool
  
  val gvar_spec_dec : LLVMsyntax.gvar_spec -> LLVMsyntax.gvar_spec -> bool
  
  val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool
  
  val product_dec : LLVMsyntax.product -> LLVMsyntax.product -> bool
  
  val products_dec : LLVMsyntax.products -> LLVMsyntax.products -> bool
  
  val namedt_dec : LLVMsyntax.namedt -> LLVMsyntax.namedt -> bool
  
  val namedts_dec : LLVMsyntax.namedts -> LLVMsyntax.namedts -> bool
  
  val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> bool
  
  val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool
  
  val module_dec : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool
  
  val modules_dec : LLVMsyntax.modules -> LLVMsyntax.modules -> bool
  
  val system_dec : LLVMsyntax.system -> LLVMsyntax.system -> bool
  
  val typEqB : LLVMsyntax.typ -> LLVMsyntax.typ -> bool
  
  val list_typEqB : LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool
  
  val idEqB : LLVMsyntax.id -> LLVMsyntax.id -> bool
  
  val constEqB : LLVMsyntax.const -> LLVMsyntax.const -> bool
  
  val list_constEqB : LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool
  
  val valueEqB : LLVMsyntax.value -> LLVMsyntax.value -> bool
  
  val paramsEqB : LLVMsyntax.params -> LLVMsyntax.params -> bool
  
  val lEqB : LLVMsyntax.l -> LLVMsyntax.l -> bool
  
  val list_value_lEqB :
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool
  
  val list_valueEqB :
    LLVMsyntax.list_sz_value -> LLVMsyntax.list_sz_value -> bool
  
  val bopEqB : LLVMsyntax.bop -> LLVMsyntax.bop -> bool
  
  val extopEqB : LLVMsyntax.extop -> LLVMsyntax.extop -> bool
  
  val condEqB : LLVMsyntax.cond -> LLVMsyntax.cond -> bool
  
  val castopEqB : LLVMsyntax.castop -> LLVMsyntax.castop -> bool
  
  val cmdEqB : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool
  
  val cmdsEqB : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool
  
  val terminatorEqB : LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool
  
  val phinodeEqB : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool
  
  val phinodesEqB :
    LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool
  
  val blockEqB : LLVMsyntax.block -> LLVMsyntax.block -> bool
  
  val blocksEqB : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool
  
  val argsEqB : LLVMsyntax.args -> LLVMsyntax.args -> bool
  
  val fheaderEqB : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool
  
  val fdecEqB : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool
  
  val fdefEqB : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool
  
  val gvarEqB : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool
  
  val productEqB : LLVMsyntax.product -> LLVMsyntax.product -> bool
  
  val productsEqB : LLVMsyntax.products -> LLVMsyntax.products -> bool
  
  val layoutEqB : LLVMsyntax.layout -> LLVMsyntax.layout -> bool
  
  val layoutsEqB : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool
  
  val moduleEqB : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool
  
  val modulesEqB : LLVMsyntax.modules -> LLVMsyntax.modules -> bool
  
  val systemEqB : LLVMsyntax.system -> LLVMsyntax.system -> bool
  
  val attributeEqB : LLVMsyntax.attribute -> LLVMsyntax.attribute -> bool
  
  val attributesEqB : LLVMsyntax.attributes -> LLVMsyntax.attributes -> bool
  
  val linkageEqB : LLVMsyntax.linkage -> LLVMsyntax.linkage -> bool
  
  val visibilityEqB : LLVMsyntax.visibility -> LLVMsyntax.visibility -> bool
  
  val callconvEqB : LLVMsyntax.callconv -> LLVMsyntax.callconv -> bool
  
  val coq_InCmdsB : LLVMsyntax.cmd -> LLVMsyntax.cmds -> bool
  
  val coq_InPhiNodesB : LLVMsyntax.phinode -> LLVMsyntax.phinodes -> bool
  
  val cmdInBlockB : LLVMsyntax.cmd -> LLVMsyntax.block -> bool
  
  val phinodeInBlockB : LLVMsyntax.phinode -> LLVMsyntax.block -> bool
  
  val terminatorInBlockB : LLVMsyntax.terminator -> LLVMsyntax.block -> bool
  
  val coq_InArgsB : LLVMsyntax.arg -> LLVMsyntax.args -> bool
  
  val argInFheaderB : LLVMsyntax.arg -> LLVMsyntax.fheader -> bool
  
  val argInFdecB : LLVMsyntax.arg -> LLVMsyntax.fdec -> bool
  
  val argInFdefB : LLVMsyntax.arg -> LLVMsyntax.fdef -> bool
  
  val coq_InBlocksB : LLVMsyntax.block -> LLVMsyntax.blocks -> bool
  
  val blockInFdefB : LLVMsyntax.block -> LLVMsyntax.fdef -> bool
  
  val coq_InProductsB : LLVMsyntax.product -> LLVMsyntax.products -> bool
  
  val productInModuleB : LLVMsyntax.product -> LLVMsyntax.coq_module -> bool
  
  val coq_InModulesB : LLVMsyntax.coq_module -> LLVMsyntax.modules -> bool
  
  val moduleInSystemB : LLVMsyntax.coq_module -> LLVMsyntax.system -> bool
  
  val productInSystemModuleB :
    LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.coq_module -> bool
  
  val blockInSystemModuleFdefB :
    LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> bool
  
  val cmdInSystemModuleFdefBlockB :
    LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val phinodeInSystemModuleFdefBlockB :
    LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val terminatorInSystemModuleFdefBlockB :
    LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val insnInSystemModuleFdefBlockB :
    LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
    LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val insnInBlockB : LLVMsyntax.insn -> LLVMsyntax.block -> bool
  
  val cmdInFdefBlockB :
    LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val phinodeInFdefBlockB :
    LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val terminatorInFdefBlockB :
    LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val insnInFdefBlockB :
    LLVMsyntax.insn -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool
  
  val cmdInBlockB_dec : LLVMsyntax.cmd -> LLVMsyntax.block -> bool
  
  val phinodeInBlockB_dec : LLVMsyntax.phinode -> LLVMsyntax.block -> bool
  
  val terminatorInBlockB_dec :
    LLVMsyntax.terminator -> LLVMsyntax.block -> bool
  
  val getParentOfCmdFromBlocks :
    LLVMsyntax.cmd -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfCmdFromFdef :
    LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfCmdFromProduct :
    LLVMsyntax.cmd -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfCmdFromProducts :
    LLVMsyntax.cmd -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfCmdFromModule :
    LLVMsyntax.cmd -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfCmdFromModules :
    LLVMsyntax.cmd -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfCmdFromSystem :
    LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val cmdHasParent : LLVMsyntax.cmd -> LLVMsyntax.system -> bool
  
  val getParentOfPhiNodeFromBlocks :
    LLVMsyntax.phinode -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromFdef :
    LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromProduct :
    LLVMsyntax.phinode -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromProducts :
    LLVMsyntax.phinode -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromModule :
    LLVMsyntax.phinode -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromModules :
    LLVMsyntax.phinode -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfPhiNodeFromSystem :
    LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val phinodeHasParent : LLVMsyntax.phinode -> LLVMsyntax.system -> bool
  
  val getParentOfTerminatorFromBlocks :
    LLVMsyntax.terminator -> LLVMsyntax.blocks -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromFdef :
    LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromProduct :
    LLVMsyntax.terminator -> LLVMsyntax.product -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromProducts :
    LLVMsyntax.terminator -> LLVMsyntax.products -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromModule :
    LLVMsyntax.terminator -> LLVMsyntax.coq_module -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromModules :
    LLVMsyntax.terminator -> LLVMsyntax.modules -> LLVMsyntax.block option
  
  val getParentOfTerminatorFromSystem :
    LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.block option
  
  val terminatoreHasParent :
    LLVMsyntax.terminator -> LLVMsyntax.system -> bool
  
  val productInModuleB_dec :
    LLVMsyntax.product -> LLVMsyntax.coq_module -> bool
  
  val getParentOfFdefFromModules :
    LLVMsyntax.fdef -> LLVMsyntax.modules -> LLVMsyntax.coq_module option
  
  val getParentOfFdefFromSystem :
    LLVMsyntax.fdef -> LLVMsyntax.system -> LLVMsyntax.coq_module option
  
  val lookupIdsViaLabelFromIdls :
    LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id list
  
  module type SigValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigUser = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigConstant = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
   end
  
  module type SigGlobalValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
   end
  
  module type SigFunction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
    
    val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val def_arg_size : LLVMsyntax.fdef -> nat
    
    val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val dec_arg_size : LLVMsyntax.fdec -> nat
   end
  
  module type SigInstruction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigReturnInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val hasReturnType : LLVMsyntax.terminator -> bool
    
    val getReturnType : LLVMsyntax.terminator -> LLVMsyntax.typ option
   end
  
  module type SigCallSite = 
   sig 
    val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val arg_size : LLVMsyntax.fdef -> nat
    
    val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option
    
    val getArgumentType : LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCallInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigBinaryOperator = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getFirstOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getSecondOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option
   end
  
  module type SigPHINode = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getNumIncomingValues : LLVMsyntax.phinode -> nat
    
    val getIncomingValueType :
      LLVMsyntax.fdef -> LLVMsyntax.phinode -> LLVMsyntax.i -> LLVMsyntax.typ
      option
   end
  
  module type SigType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigDerivedType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigFunctionType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val getNumParams : LLVMsyntax.typ -> nat option
    
    val isVarArg : LLVMsyntax.typ -> bool
    
    val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCompositeType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigSequentialType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module type SigArrayType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getNumElements : LLVMsyntax.typ -> nat
   end
  
  module Value : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module User : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module Constant : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ
      -> LLVMsyntax.typ option
    
    val gen_utyps_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps :
      LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ -> LLVMsyntax.typ
      option
    
    val typs2utyps_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ option
    
    val typ2utyp' :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val subst_typ :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_typs :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ
    
    val subst_typ_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_nts_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.namedts ->
      (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module GlobalValue : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ
      -> LLVMsyntax.typ option
    
    val gen_utyps_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps :
      LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ -> LLVMsyntax.typ
      option
    
    val typs2utyps_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ option
    
    val typ2utyp' :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val subst_typ :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_typs :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ
    
    val subst_typ_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_nts_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.namedts ->
      (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module Function : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
    
    val getList_typ : LLVMsyntax.list_const -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ
      -> LLVMsyntax.typ option
    
    val gen_utyps_maps_aux :
      LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ option
    
    val gen_utyp_maps :
      LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ -> LLVMsyntax.typ
      option
    
    val typs2utyps_aux :
      (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ option
    
    val typ2utyp' :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val subst_typ :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_typs :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
      LLVMsyntax.list_typ
    
    val subst_typ_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ
    
    val subst_nts_by_nts :
      LLVMsyntax.namedts -> LLVMsyntax.namedts ->
      (LLVMsyntax.id*LLVMsyntax.typ) list
    
    val typ2utyp :
      LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val def_arg_size : LLVMsyntax.fdef -> nat
    
    val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val dec_arg_size : LLVMsyntax.fdec -> nat
   end
  
  module Instruction : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module ReturnInst : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val hasReturnType : LLVMsyntax.terminator -> bool
    
    val getReturnType : LLVMsyntax.terminator -> LLVMsyntax.typ option
   end
  
  module CallSite : 
   sig 
    val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val arg_size : LLVMsyntax.fdef -> nat
    
    val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option
    
    val getArgumentType : LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option
   end
  
  module CallInst : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module BinaryOperator : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getFirstOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getSecondOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option
   end
  
  module PHINode : 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getNumIncomingValues : LLVMsyntax.phinode -> nat
    
    val getIncomingValueType :
      LLVMsyntax.fdef -> LLVMsyntax.phinode -> nat -> LLVMsyntax.typ option
   end
  
  module Typ : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module DerivedType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module FunctionType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val getNumParams : LLVMsyntax.typ -> nat option
    
    val isVarArg : LLVMsyntax.typ -> bool
    
    val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option
   end
  
  module CompositeType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module SequentialType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module ArrayType : 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val isSizedListTyp : LLVMsyntax.list_typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getNumElements : LLVMsyntax.typ -> nat
   end
  
  val typ2memory_chunk : LLVMsyntax.typ -> memory_chunk option
  
  type reflect =
    | ReflectT
    | ReflectF
  
  val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1
  
  val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1
 end

