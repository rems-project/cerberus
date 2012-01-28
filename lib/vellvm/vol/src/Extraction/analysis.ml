open Datatypes
open Kildall
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Specif
open Infrastructure
open Syntax

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val successors_blocks : LLVMsyntax.blocks -> LLVMsyntax.ls ATree.t **)

let rec successors_blocks = function
  | [] -> ATree.empty
  | b::bs' ->
      let LLVMsyntax.Coq_block_intro (l0, p, c, tmn) = b in
      ATree.set l0 (LLVMinfra.successors_terminator tmn)
        (successors_blocks bs')

(** val successors : LLVMsyntax.fdef -> LLVMsyntax.ls ATree.t **)

let successors = function
  | LLVMsyntax.Coq_fdef_intro (f0, bs) -> successors_blocks bs

(** val transfer :
    AtomImpl.atom set -> LLVMsyntax.l -> Dominators.t -> Dominators.t **)

let transfer bound0 lbl before =
  Dominators.add bound0 before lbl

(** val bound_blocks : LLVMsyntax.blocks -> AtomImpl.atom set **)

let rec bound_blocks = function
  | [] -> empty_set
  | b::bs' ->
      let LLVMsyntax.Coq_block_intro (l0, p, c, tmn) = b in
      l0::(bound_blocks bs')

(** val bound_fdef : LLVMsyntax.fdef -> AtomImpl.atom set **)

let bound_fdef = function
  | LLVMsyntax.Coq_fdef_intro (f0, bs) -> bound_blocks bs

(** val entry_dom :
    LLVMsyntax.block list -> ((LLVMsyntax.l*Dominators.coq_BoundedSet)
    option, __) sigT **)

let entry_dom = function
  | [] -> Coq_existT (None, (Obj.magic __))
  | b::bs0 ->
      let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
      Coq_existT ((Some (l0,[])), (Obj.magic __))

module DomDS = Dataflow_Solver_Var_Top(AtomNodeSet)

(** val dom_analyze : LLVMsyntax.fdef -> Dominators.t AMap.t **)

let dom_analyze = function
  | LLVMsyntax.Coq_fdef_intro (f0, bs) ->
      let bound0 = bound_blocks bs in
      let top0 = Dominators.top bound0 in
      let Coq_existT (x, y) = entry_dom bs in
      (match x with
         | Some p ->
             let le,start = p in
             (match DomDS.fixpoint bound0 (successors_blocks bs)
                      (Obj.magic (transfer bound0))
                      ((le,(Obj.magic start))::[]) with
                | Some res -> Obj.magic res
                | None -> AMap.set le start (AMap.init top0))
         | None -> AMap.init top0)

module ReachDS = Dataflow_Solver(LBoolean)(AtomNodeSet)

(** val areachable_aux : LLVMsyntax.fdef -> bool AMap.t option **)

let areachable_aux f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (le, p, c, t0) = b in
        ReachDS.fixpoint (successors f) (fun pc r -> r) ((le,true)::[])
    | None -> None

(** val areachable : LLVMsyntax.fdef -> bool AMap.t **)

let areachable f =
  match areachable_aux f with
    | Some rs -> rs
    | None -> AMap.init true

module EntryDomsOthers = 
 struct 
  (** val bound : LLVMsyntax.blocks -> AtomImpl.atom set **)
  
  let bound bs =
    bound_blocks bs
  
  (** val predecessors : LLVMsyntax.blocks -> AtomImpl.atom list ATree.t **)
  
  let predecessors bs =
    make_predecessors (successors_blocks bs)
  
  (** val transf :
      LLVMsyntax.blocks -> LLVMsyntax.l -> Dominators.t -> Dominators.t **)
  
  let transf bs =
    transfer (bound bs)
  
  (** val top : LLVMsyntax.blocks -> Dominators.t **)
  
  let top bs =
    Dominators.top (bound bs)
  
  (** val bot : LLVMsyntax.blocks -> Dominators.t **)
  
  let bot bs =
    Dominators.bot (bound bs)
  
  type dt = DomDS.dt
  
  (** val lub_of_preds :
      LLVMsyntax.blocks -> dt AMap.t -> AtomImpl.atom -> dt **)
  
  let lub_of_preds bs res n =
    Obj.magic
      (Dominators.lubs (bound bs)
        (map (fun p -> transf bs p (AMap.get p (Obj.magic res)))
          (successors_list (predecessors bs) n)))
 end

(** val cmds_dominates_cmd :
    LLVMsyntax.cmds -> LLVMsyntax.id -> AtomImpl.atom list **)

let rec cmds_dominates_cmd cs id0 =
  match cs with
    | [] -> []
    | c1::cs' ->
        let ctx = cmds_dominates_cmd cs' id0 in
        if AtomImpl.eq_atom_dec (LLVMinfra.getCmdLoc c1) id0
        then []
        else (match LLVMinfra.getCmdID c1 with
                | Some id1 -> id1::ctx
                | None -> ctx)

(** val inscope_of_block :
    LLVMsyntax.fdef -> LLVMsyntax.l -> AtomImpl.atom list option ->
    LLVMsyntax.l -> AtomImpl.atom list option **)

let inscope_of_block f l1 opt_ctx lbl =
  match opt_ctx with
    | Some ctx ->
        (match LLVMinfra.lookupBlockViaLabelFromFdef f lbl with
           | Some b ->
               if AtomImpl.eq_atom_dec lbl l1
               then Some ctx
               else Some (app (LLVMinfra.getBlockIDs b) ctx)
           | None -> None)
    | None -> None

(** val inscope_of_id :
    LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.id -> AtomImpl.atom
    list option **)

let inscope_of_id f b1 id0 =
  let LLVMsyntax.Coq_block_intro (l1, ps, cs, t0) = b1 in
  let LLVMsyntax.Coq_fdef_intro (f0, b) = f in
  let LLVMsyntax.Coq_fheader_intro (f1, t1, i, la, v) = f0 in
  fold_left (inscope_of_block f l1) (AMap.get l1 (dom_analyze f)) (Some
    (app (LLVMinfra.getPhiNodesIDs ps)
      (app (cmds_dominates_cmd cs id0) (LLVMinfra.getArgsIDs la))))

(** val inscope_of_cmd :
    LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.cmd -> AtomImpl.atom
    list option **)

let inscope_of_cmd f b1 c =
  let id0 = LLVMinfra.getCmdLoc c in inscope_of_id f b1 id0

(** val inscope_of_tmn :
    LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.terminator ->
    AtomImpl.atom list option **)

let inscope_of_tmn f b1 tmn =
  let LLVMsyntax.Coq_block_intro (l1, ps, cs, t0) = b1 in
  let LLVMsyntax.Coq_fdef_intro (f0, b) = f in
  let LLVMsyntax.Coq_fheader_intro (f1, t1, i, la, v) = f0 in
  fold_left (inscope_of_block f l1) (AMap.get l1 (dom_analyze f)) (Some
    (app (LLVMinfra.getPhiNodesIDs ps)
      (app (LLVMinfra.getCmdsIDs cs) (LLVMinfra.getArgsIDs la))))

(** val defs_dominate :
    LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.block ->
    LLVMsyntax.insn -> AtomImpl.atom list option **)

let defs_dominate f curb incomingb = function
  | LLVMsyntax.Coq_insn_phinode p ->
      let LLVMsyntax.Coq_block_intro (l0, p0, c, tmn) = incomingb in
      inscope_of_tmn f incomingb tmn
  | LLVMsyntax.Coq_insn_cmd c -> inscope_of_cmd f curb c
  | LLVMsyntax.Coq_insn_terminator tmn -> inscope_of_tmn f curb tmn

