open MetatheoryAtom
open Eq_tv_dec
open Infrastructure
open Symexe_def
open Syntax

(** val tv_cmds : SimpleSE.nbranch list -> SimpleSE.nbranch list -> bool **)

let tv_cmds nbs1 nbs2 =
  LLVMinfra.sumbool2bool
    (sstate_dec (SimpleSE.se_cmds SimpleSE.sstate_init nbs1)
      (SimpleSE.se_cmds SimpleSE.sstate_init nbs2))

(** val tv_subblock : SimpleSE.subblock -> SimpleSE.subblock -> bool **)

let tv_subblock sb1 sb2 =
  let { SimpleSE.coq_NBs = nbs1; SimpleSE.call_cmd = call1 } = sb1 in
  let { SimpleSE.coq_NBs = nbs2; SimpleSE.call_cmd = call2 } = sb2 in
  let st1 = SimpleSE.se_cmds SimpleSE.sstate_init nbs1 in
  let st2 = SimpleSE.se_cmds SimpleSE.sstate_init nbs2 in
  if LLVMinfra.sumbool2bool (sstate_dec st1 st2)
  then LLVMinfra.sumbool2bool (LLVMinfra.cmd_dec call1 call2)
  else false

(** val tv_subblocks :
    SimpleSE.subblock list -> SimpleSE.subblock list -> bool **)

let rec tv_subblocks sbs1 sbs2 =
  match sbs1 with
    | [] -> (match sbs2 with
               | [] -> true
               | s::l -> false)
    | sb1::sbs1' ->
        (match sbs2 with
           | [] -> false
           | sb2::sbs2' ->
               if tv_subblock sb1 sb2
               then tv_subblocks sbs1' sbs2'
               else false)

(** val tv_phinodes : LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool **)

let rec tv_phinodes ps1 ps2 =
  match ps1 with
    | [] -> (match ps2 with
               | [] -> true
               | p::l -> false)
    | p1::ps1' ->
        (match ps2 with
           | [] -> false
           | p2::ps2' ->
               if LLVMinfra.sumbool2bool (LLVMinfra.phinode_dec p1 p2)
               then tv_phinodes ps1' ps2'
               else false)

(** val tv_block : LLVMsyntax.block -> LLVMsyntax.block -> bool **)

let tv_block b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) = b1 in
  let LLVMsyntax.Coq_block_intro (l2, ps2, cs2, tmn2) = b2 in
  let p = SimpleSE.cmds2sbs cs1 in
  let p0 = SimpleSE.cmds2sbs cs2 in
  let sbs1,nbs1 = p in
  let sbs2,nbs2 = p0 in
  if if if if LLVMinfra.sumbool2bool (AtomImpl.eq_atom_dec l1 l2)
           then tv_phinodes ps1 ps2
           else false
        then tv_subblocks sbs1 sbs2
        else false
     then tv_cmds nbs1 nbs2
     else false
  then LLVMinfra.sumbool2bool (LLVMinfra.terminator_dec tmn1 tmn2)
  else false

(** val tv_blocks : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)

let rec tv_blocks bs1 bs2 =
  match bs1 with
    | [] -> (match bs2 with
               | [] -> true
               | b::l -> false)
    | b1::bs1' ->
        (match bs2 with
           | [] -> false
           | b2::bs2' ->
               if tv_block b1 b2 then tv_blocks bs1' bs2' else false)

(** val tv_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)

let tv_fdef f1 f2 =
  let LLVMsyntax.Coq_fdef_intro (fh1, lb1) = f1 in
  let LLVMsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  if LLVMinfra.sumbool2bool (LLVMinfra.fheader_dec fh1 fh2)
  then tv_blocks lb1 lb2
  else false

(** val tv_products : LLVMsyntax.products -> LLVMsyntax.products -> bool **)

let rec tv_products ps1 ps2 =
  match ps1 with
    | [] -> (match ps2 with
               | [] -> true
               | p::l -> false)
    | p::ps1' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gvar1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_gvar gvar2 ->
                             if LLVMinfra.sumbool2bool
                                  (LLVMinfra.gvar_dec gvar1 gvar2)
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false))
           | LLVMsyntax.Coq_product_fdec f1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdec f2 ->
                             if LLVMinfra.sumbool2bool
                                  (LLVMinfra.fdec_dec f1 f2)
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false))
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match ps2 with
                  | [] -> false
                  | p0::ps2' ->
                      (match p0 with
                         | LLVMsyntax.Coq_product_fdef f2 ->
                             if tv_fdef f1 f2
                             then tv_products ps1' ps2'
                             else false
                         | _ -> false)))

(** val tv_module :
    LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)

let tv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (los1, nts1, ps1) = m1 in
  let LLVMsyntax.Coq_module_intro (los2, nts2, ps2) = m2 in
  if if LLVMinfra.sumbool2bool (LLVMinfra.layouts_dec los1 los2)
     then LLVMinfra.sumbool2bool (LLVMinfra.namedts_dec nts1 nts2)
     else false
  then tv_products ps1 ps2
  else false

(** val tv_system : LLVMsyntax.system -> LLVMsyntax.system -> bool **)

let rec tv_system s1 s2 =
  match s1 with
    | [] -> (match s2 with
               | [] -> true
               | m::l -> false)
    | m1::s1' ->
        (match s2 with
           | [] -> false
           | m2::s2' -> if tv_module m1 m2 then tv_system s1' s2' else false)

