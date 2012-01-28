open MetatheoryAtom
open Eq_tv_dec
open Infrastructure
open Symexe_def
open Syntax

val tv_cmds : SimpleSE.nbranch list -> SimpleSE.nbranch list -> bool

val tv_subblock : SimpleSE.subblock -> SimpleSE.subblock -> bool

val tv_subblocks : SimpleSE.subblock list -> SimpleSE.subblock list -> bool

val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool

val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool

val tv_blocks : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool

val tv_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool

val tv_products : LLVMsyntax.products -> LLVMsyntax.products -> bool

val tv_module : LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool

val tv_system : LLVMsyntax.system -> LLVMsyntax.system -> bool

