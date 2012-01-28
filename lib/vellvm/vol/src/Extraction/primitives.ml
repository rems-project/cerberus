open Coqlib
open Datatypes
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Dtree
open Infrastructure
open Syntax

(** val subst_value :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.value **)

let subst_value id' v' v = match v with
  | LLVMsyntax.Coq_value_id id1 -> if LLVMinfra.id_dec id1 id' then v' else v
  | LLVMsyntax.Coq_value_const c -> v

(** val subst_list_value :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.list_sz_value ->
    LLVMsyntax.list_sz_value **)

let rec subst_list_value id' v' = function
  | LLVMsyntax.Nil_list_sz_value -> LLVMsyntax.Nil_list_sz_value
  | LLVMsyntax.Cons_list_sz_value (sz0, v0, tl) ->
      LLVMsyntax.Cons_list_sz_value (sz0, (subst_value id' v' v0),
      (subst_list_value id' v' tl))

(** val subst_cmd :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let subst_cmd id' v' = function
  | LLVMsyntax.Coq_insn_bop (id0, t0, bop0, v1, v2) ->
      LLVMsyntax.Coq_insn_bop (id0, t0, bop0, (subst_value id' v' v1),
      (subst_value id' v' v2))
  | LLVMsyntax.Coq_insn_fbop (id0, fbop0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fbop (id0, fbop0, fp0, (subst_value id' v' v1),
      (subst_value id' v' v2))
  | LLVMsyntax.Coq_insn_extractvalue (id0, t0, v, cnts) ->
      LLVMsyntax.Coq_insn_extractvalue (id0, t0, (subst_value id' v' v),
      cnts)
  | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cnts) ->
      LLVMsyntax.Coq_insn_insertvalue (id0, t1, (subst_value id' v' v1), t2,
      (subst_value id' v' v2), cnts)
  | LLVMsyntax.Coq_insn_malloc (id0, t0, v, al) -> LLVMsyntax.Coq_insn_malloc
      (id0, t0, (subst_value id' v' v), al)
  | LLVMsyntax.Coq_insn_free (id0, t0, v) -> LLVMsyntax.Coq_insn_free (id0,
      t0, (subst_value id' v' v))
  | LLVMsyntax.Coq_insn_alloca (id0, t0, v, al) -> LLVMsyntax.Coq_insn_alloca
      (id0, t0, (subst_value id' v' v), al)
  | LLVMsyntax.Coq_insn_load (id0, t0, v, al) -> LLVMsyntax.Coq_insn_load
      (id0, t0, (subst_value id' v' v), al)
  | LLVMsyntax.Coq_insn_store (id0, t1, v1, v2, al) ->
      LLVMsyntax.Coq_insn_store (id0, t1, (subst_value id' v' v1),
      (subst_value id' v' v2), al)
  | LLVMsyntax.Coq_insn_gep (id0, ib0, t0, v, vs) -> LLVMsyntax.Coq_insn_gep
      (id0, ib0, t0, (subst_value id' v' v), (subst_list_value id' v' vs))
  | LLVMsyntax.Coq_insn_trunc (id0, top0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_trunc (id0, top0, t1, (subst_value id' v' v1), t2)
  | LLVMsyntax.Coq_insn_ext (id0, eop0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_ext (id0, eop0, t1, (subst_value id' v' v1), t2)
  | LLVMsyntax.Coq_insn_cast (id0, cop0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_cast (id0, cop0, t1, (subst_value id' v' v1), t2)
  | LLVMsyntax.Coq_insn_icmp (id0, t0, cond0, v1, v2) ->
      LLVMsyntax.Coq_insn_icmp (id0, t0, cond0, (subst_value id' v' v1),
      (subst_value id' v' v2))
  | LLVMsyntax.Coq_insn_fcmp (id0, fcond0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fcmp (id0, fcond0, fp0, (subst_value id' v' v1),
      (subst_value id' v' v2))
  | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) ->
      LLVMsyntax.Coq_insn_select (id0, (subst_value id' v' v0), t0,
      (subst_value id' v' v1), (subst_value id' v' v2))
  | LLVMsyntax.Coq_insn_call (id0, noret0, cl0, t1, v1, ps) ->
      LLVMsyntax.Coq_insn_call (id0, noret0, cl0, t1,
      (subst_value id' v' v1),
      (map (fun p -> let t0,v = p in t0,(subst_value id' v' v)) ps))

(** val subst_tmn :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.terminator ->
    LLVMsyntax.terminator **)

let subst_tmn id' v' tmn = match tmn with
  | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> LLVMsyntax.Coq_insn_return
      (id0, t0, (subst_value id' v' v0))
  | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> LLVMsyntax.Coq_insn_br (id0,
      (subst_value id' v' v0), l1, l2)
  | _ -> tmn

(** val subst_list_value_l :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.list_value_l ->
    LLVMsyntax.list_value_l **)

let rec subst_list_value_l id' v' = function
  | LLVMsyntax.Nil_list_value_l -> LLVMsyntax.Nil_list_value_l
  | LLVMsyntax.Cons_list_value_l (v0, l1, tl) -> LLVMsyntax.Cons_list_value_l
      ((subst_value id' v' v0), l1, (subst_list_value_l id' v' tl))

(** val subst_phi :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.phinode ->
    LLVMsyntax.phinode **)

let subst_phi id' v' = function
  | LLVMsyntax.Coq_insn_phi (id0, t0, vls) -> LLVMsyntax.Coq_insn_phi (id0,
      t0, (subst_list_value_l id' v' vls))

(** val subst_insn :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.insn -> LLVMsyntax.insn **)

let subst_insn id' v' = function
  | LLVMsyntax.Coq_insn_phinode pn -> LLVMsyntax.Coq_insn_phinode
      (subst_phi id' v' pn)
  | LLVMsyntax.Coq_insn_cmd c -> LLVMsyntax.Coq_insn_cmd (subst_cmd id' v' c)
  | LLVMsyntax.Coq_insn_terminator tmn -> LLVMsyntax.Coq_insn_terminator
      (subst_tmn id' v' tmn)

(** val subst_block :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.block -> LLVMsyntax.block **)

let subst_block id' v' = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro (l0, (map (subst_phi id' v') ps0),
      (map (subst_cmd id' v') cs0), (subst_tmn id' v' tmn0))

(** val subst_fdef :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let subst_fdef id' v' = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
      (map (subst_block id' v') bs))

(** val csubst_fdef :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let csubst_fdef id' cst' =
  subst_fdef id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_block :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.block -> LLVMsyntax.block **)

let csubst_block id' cst' =
  subst_block id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_phi :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.phinode ->
    LLVMsyntax.phinode **)

let csubst_phi id' cst' =
  subst_phi id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_cmd :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let csubst_cmd id' cst' =
  subst_cmd id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_tmn :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.terminator ->
    LLVMsyntax.terminator **)

let csubst_tmn id' cst' =
  subst_tmn id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_insn :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.insn -> LLVMsyntax.insn **)

let csubst_insn id' cst' =
  subst_insn id' (LLVMsyntax.Coq_value_const cst')

(** val csubst_value :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.value -> LLVMsyntax.value **)

let csubst_value id' cst' =
  subst_value id' (LLVMsyntax.Coq_value_const cst')

(** val isubst_fdef :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let isubst_fdef id1 id2 =
  subst_fdef id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_block :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block **)

let isubst_block id1 id2 =
  subst_block id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_phi :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.phinode ->
    LLVMsyntax.phinode **)

let isubst_phi id1 id2 =
  subst_phi id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_cmd :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let isubst_cmd id1 id2 =
  subst_cmd id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_tmn :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.terminator ->
    LLVMsyntax.terminator **)

let isubst_tmn id1 id2 =
  subst_tmn id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_insn :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.insn -> LLVMsyntax.insn **)

let isubst_insn id1 id2 =
  subst_insn id1 (LLVMsyntax.Coq_value_id id2)

(** val isubst_value :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value **)

let isubst_value id1 id2 =
  subst_value id1 (LLVMsyntax.Coq_value_id id2)

(** val remove_phinodes :
    LLVMsyntax.id -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes **)

let remove_phinodes id' ps =
  filter (fun p ->
    negb (proj_sumbool (LLVMinfra.id_dec (LLVMinfra.getPhiNodeID p) id'))) ps

(** val remove_cmds : LLVMsyntax.id -> LLVMsyntax.cmds -> LLVMsyntax.cmds **)

let remove_cmds id' cs =
  filter (fun c ->
    negb (proj_sumbool (LLVMinfra.id_dec (LLVMinfra.getCmdLoc c) id'))) cs

(** val remove_block :
    LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block **)

let remove_block id' = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro (l0, (remove_phinodes id' ps0),
      (remove_cmds id' cs0), tmn0)

(** val remove_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let remove_fdef id' = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
      (map (remove_block id') bs))

(** val used_in_value : LLVMsyntax.id -> LLVMsyntax.value -> bool **)

let used_in_value id0 = function
  | LLVMsyntax.Coq_value_id id1 -> proj_sumbool (LLVMinfra.id_dec id1 id0)
  | LLVMsyntax.Coq_value_const c -> false

(** val used_in_list_value :
    LLVMsyntax.id -> LLVMsyntax.list_sz_value -> bool **)

let rec used_in_list_value id0 = function
  | LLVMsyntax.Nil_list_sz_value -> false
  | LLVMsyntax.Cons_list_sz_value (s, v0, tl) ->
      if used_in_value id0 v0 then true else used_in_list_value id0 tl

(** val used_in_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> bool **)

let used_in_cmd id' = function
  | LLVMsyntax.Coq_insn_bop (i, b, s, v1, v2) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_fbop (i, f, f0, v1, v2) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_extractvalue (i, t0, v, l0) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_insertvalue (i, t0, v1, t1, v2, l0) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_malloc (i, t0, v, a) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_free (i, t0, v) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_alloca (i, t0, v, a) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_load (i, t0, v, a) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_store (i, t0, v1, v2, a) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_gep (i, i0, t0, v, vs) ->
      if used_in_value id' v then true else used_in_list_value id' vs
  | LLVMsyntax.Coq_insn_trunc (i, t0, t1, v, t2) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_ext (i, e, t0, v, t1) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_cast (i, c0, t0, v, t1) -> used_in_value id' v
  | LLVMsyntax.Coq_insn_icmp (i, c0, t0, v1, v2) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_fcmp (i, f, f0, v1, v2) ->
      if used_in_value id' v1 then true else used_in_value id' v2
  | LLVMsyntax.Coq_insn_select (i, v0, t0, v1, v2) ->
      if if used_in_value id' v0 then true else used_in_value id' v1
      then true
      else used_in_value id' v2
  | LLVMsyntax.Coq_insn_call (i, n, c0, t0, v1, ps) ->
      if used_in_value id' v1
      then true
      else fold_left (fun acc p ->
             let y,v = p in if used_in_value id' v then true else acc) ps
             false

(** val used_in_tmn : LLVMsyntax.id -> LLVMsyntax.terminator -> bool **)

let used_in_tmn id' = function
  | LLVMsyntax.Coq_insn_return (i, t0, v0) -> used_in_value id' v0
  | LLVMsyntax.Coq_insn_br (i, v0, l0, l1) -> used_in_value id' v0
  | _ -> false

(** val used_in_list_value_l :
    LLVMsyntax.id -> LLVMsyntax.list_value_l -> bool **)

let rec used_in_list_value_l id' = function
  | LLVMsyntax.Nil_list_value_l -> false
  | LLVMsyntax.Cons_list_value_l (v0, l1, tl) ->
      if used_in_value id' v0 then true else used_in_list_value_l id' tl

(** val used_in_phi : LLVMsyntax.id -> LLVMsyntax.phinode -> bool **)

let used_in_phi id' = function
  | LLVMsyntax.Coq_insn_phi (i, t0, vls) -> used_in_list_value_l id' vls

(** val used_in_insn : LLVMsyntax.id -> LLVMsyntax.insn -> bool **)

let used_in_insn id' = function
  | LLVMsyntax.Coq_insn_phinode p -> used_in_phi id' p
  | LLVMsyntax.Coq_insn_cmd c -> used_in_cmd id' c
  | LLVMsyntax.Coq_insn_terminator tmn -> used_in_tmn id' tmn

(** val used_in_block : LLVMsyntax.id -> LLVMsyntax.block -> bool **)

let used_in_block id' = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      if if fold_left (fun re p -> if re then true else used_in_phi id' p)
              ps0 false
         then true
         else fold_left (fun re c -> if re then true else used_in_cmd id' c)
                cs0 false
      then true
      else used_in_tmn id' tmn0

(** val used_in_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> bool **)

let used_in_fdef id' = function
  | LLVMsyntax.Coq_fdef_intro (f0, bs) ->
      fold_left (fun re b -> if re then true else used_in_block id' b) bs
        false

(** val insert_cmds :
    nat -> LLVMsyntax.cmd -> LLVMsyntax.cmds -> LLVMsyntax.cmds **)

let insert_cmds n c cs =
  app (firstn n cs) (c::(skipn n cs))

(** val insert_block :
    LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.block ->
    LLVMsyntax.block **)

let insert_block l1 n c = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro (l0, ps0,
      (if LLVMinfra.l_dec l1 l0 then insert_cmds n c cs0 else cs0), tmn0)

(** val insert_fdef :
    LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.fdef ->
    LLVMsyntax.fdef **)

let insert_fdef l1 n c = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
      (map (insert_block l1 n c) bs))

(** val rename_id :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id **)

let rename_id id1 id2 id0 =
  if LLVMinfra.id_dec id0 id1 then id2 else id0

(** val rename_value :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value **)

let rename_value id1 id2 v = match v with
  | LLVMsyntax.Coq_value_id id0 -> LLVMsyntax.Coq_value_id
      (rename_id id1 id2 id0)
  | LLVMsyntax.Coq_value_const c -> v

(** val rename_list_value :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.list_sz_value ->
    LLVMsyntax.list_sz_value **)

let rec rename_list_value id1 id2 = function
  | LLVMsyntax.Nil_list_sz_value -> LLVMsyntax.Nil_list_sz_value
  | LLVMsyntax.Cons_list_sz_value (sz0, v0, tl) ->
      LLVMsyntax.Cons_list_sz_value (sz0, (rename_value id1 id2 v0),
      (rename_list_value id1 id2 tl))

(** val rename_cmd :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let rename_cmd id1 id2 = function
  | LLVMsyntax.Coq_insn_bop (id0, t0, bop0, v1, v2) ->
      LLVMsyntax.Coq_insn_bop ((rename_id id1 id2 id0), t0, bop0,
      (rename_value id1 id2 v1), (rename_value id1 id2 v2))
  | LLVMsyntax.Coq_insn_fbop (id0, fbop0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fbop ((rename_id id1 id2 id0), fbop0, fp0,
      (rename_value id1 id2 v1), (rename_value id1 id2 v2))
  | LLVMsyntax.Coq_insn_extractvalue (id0, t0, v, cnts) ->
      LLVMsyntax.Coq_insn_extractvalue ((rename_id id1 id2 id0), t0,
      (rename_value id1 id2 v), cnts)
  | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cnts) ->
      LLVMsyntax.Coq_insn_insertvalue ((rename_id id1 id2 id0), t1,
      (rename_value id1 id2 v1), t2, (rename_value id1 id2 v2), cnts)
  | LLVMsyntax.Coq_insn_malloc (id0, t0, v, al) -> LLVMsyntax.Coq_insn_malloc
      ((rename_id id1 id2 id0), t0, (rename_value id1 id2 v), al)
  | LLVMsyntax.Coq_insn_free (id0, t0, v) -> LLVMsyntax.Coq_insn_free
      ((rename_id id1 id2 id0), t0, (rename_value id1 id2 v))
  | LLVMsyntax.Coq_insn_alloca (id0, t0, v, al) -> LLVMsyntax.Coq_insn_alloca
      ((rename_id id1 id2 id0), t0, (rename_value id1 id2 v), al)
  | LLVMsyntax.Coq_insn_load (id0, t0, v, al) -> LLVMsyntax.Coq_insn_load
      ((rename_id id1 id2 id0), t0, (rename_value id1 id2 v), al)
  | LLVMsyntax.Coq_insn_store (id0, t1, v1, v2, al) ->
      LLVMsyntax.Coq_insn_store ((rename_id id1 id2 id0), t1,
      (rename_value id1 id2 v1), (rename_value id1 id2 v2), al)
  | LLVMsyntax.Coq_insn_gep (id0, ib0, t0, v, vs) -> LLVMsyntax.Coq_insn_gep
      ((rename_id id1 id2 id0), ib0, t0, (rename_value id1 id2 v),
      (rename_list_value id1 id2 vs))
  | LLVMsyntax.Coq_insn_trunc (id0, top0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_trunc ((rename_id id1 id2 id0), top0, t1,
      (rename_value id1 id2 v1), t2)
  | LLVMsyntax.Coq_insn_ext (id0, eop0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_ext ((rename_id id1 id2 id0), eop0, t1,
      (rename_value id1 id2 v1), t2)
  | LLVMsyntax.Coq_insn_cast (id0, cop0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_cast ((rename_id id1 id2 id0), cop0, t1,
      (rename_value id1 id2 v1), t2)
  | LLVMsyntax.Coq_insn_icmp (id0, t0, cond0, v1, v2) ->
      LLVMsyntax.Coq_insn_icmp ((rename_id id1 id2 id0), t0, cond0,
      (rename_value id1 id2 v1), (rename_value id1 id2 v2))
  | LLVMsyntax.Coq_insn_fcmp (id0, fcond0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fcmp ((rename_id id1 id2 id0), fcond0, fp0,
      (rename_value id1 id2 v1), (rename_value id1 id2 v2))
  | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) ->
      LLVMsyntax.Coq_insn_select ((rename_id id1 id2 id0),
      (rename_value id1 id2 v0), t0, (rename_value id1 id2 v1),
      (rename_value id1 id2 v2))
  | LLVMsyntax.Coq_insn_call (id0, noret0, cl0, t1, v1, ps) ->
      LLVMsyntax.Coq_insn_call ((rename_id id1 id2 id0), noret0, cl0, t1,
      (rename_value id1 id2 v1),
      (map (fun p -> let t0,v = p in t0,(rename_value id1 id2 v)) ps))

(** val rename_tmn :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.terminator ->
    LLVMsyntax.terminator **)

let rename_tmn id1 id2 = function
  | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> LLVMsyntax.Coq_insn_return
      ((rename_id id1 id2 id0), t0, (rename_value id1 id2 v0))
  | LLVMsyntax.Coq_insn_return_void id0 -> LLVMsyntax.Coq_insn_return_void
      (rename_id id1 id2 id0)
  | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> LLVMsyntax.Coq_insn_br
      ((rename_id id1 id2 id0), (rename_value id1 id2 v0), l1, l2)
  | LLVMsyntax.Coq_insn_br_uncond (id0, l1) -> LLVMsyntax.Coq_insn_br_uncond
      ((rename_id id1 id2 id0), l1)
  | LLVMsyntax.Coq_insn_unreachable id0 -> LLVMsyntax.Coq_insn_unreachable
      (rename_id id1 id2 id0)

(** val rename_list_value_l :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.list_value_l ->
    LLVMsyntax.list_value_l **)

let rec rename_list_value_l id1 id2 = function
  | LLVMsyntax.Nil_list_value_l -> LLVMsyntax.Nil_list_value_l
  | LLVMsyntax.Cons_list_value_l (v0, l1, tl) -> LLVMsyntax.Cons_list_value_l
      ((rename_value id1 id2 v0), l1, (rename_list_value_l id1 id2 tl))

(** val rename_phi :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.phinode ->
    LLVMsyntax.phinode **)

let rename_phi id1 id2 = function
  | LLVMsyntax.Coq_insn_phi (id0, t0, vls) -> LLVMsyntax.Coq_insn_phi
      ((rename_id id1 id2 id0), t0, (rename_list_value_l id1 id2 vls))

(** val rename_insn :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.insn -> LLVMsyntax.insn **)

let rename_insn id1 id2 = function
  | LLVMsyntax.Coq_insn_phinode pn -> LLVMsyntax.Coq_insn_phinode
      (rename_phi id1 id2 pn)
  | LLVMsyntax.Coq_insn_cmd c -> LLVMsyntax.Coq_insn_cmd
      (rename_cmd id1 id2 c)
  | LLVMsyntax.Coq_insn_terminator tmn -> LLVMsyntax.Coq_insn_terminator
      (rename_tmn id1 id2 tmn)

(** val rename_block :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block **)

let rename_block id1 id2 = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro (l0, (map (rename_phi id1 id2) ps0),
      (map (rename_cmd id1 id2) cs0), (rename_tmn id1 id2 tmn0))

(** val rename_fheader :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fheader ->
    LLVMsyntax.fheader **)

let rename_fheader id1 id2 = function
  | LLVMsyntax.Coq_fheader_intro (fr, t0, fid, la, va) ->
      LLVMsyntax.Coq_fheader_intro (fr, t0, fid,
      (map (fun a -> let p,id0 = a in p,(rename_id id1 id2 id0)) la), va)

(** val rename_fdef :
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let rename_fdef id1 id2 = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro
      ((rename_fheader id1 id2 fh), (map (rename_block id1 id2) bs))

(** val gen_fresh_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let gen_fresh_cmd id0 = function
  | LLVMsyntax.Coq_insn_bop (i, t0, bop0, v1, v2) -> LLVMsyntax.Coq_insn_bop
      (id0, t0, bop0, v1, v2)
  | LLVMsyntax.Coq_insn_fbop (i, fbop0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fbop (id0, fbop0, fp0, v1, v2)
  | LLVMsyntax.Coq_insn_extractvalue (i, t0, v, cnts) ->
      LLVMsyntax.Coq_insn_extractvalue (id0, t0, v, cnts)
  | LLVMsyntax.Coq_insn_insertvalue (i, t1, v1, t2, v2, cnts) ->
      LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cnts)
  | LLVMsyntax.Coq_insn_malloc (i, t0, v, al) -> LLVMsyntax.Coq_insn_malloc
      (id0, t0, v, al)
  | LLVMsyntax.Coq_insn_free (i, t0, v) -> LLVMsyntax.Coq_insn_free (id0, t0,
      v)
  | LLVMsyntax.Coq_insn_alloca (i, t0, v, al) -> LLVMsyntax.Coq_insn_alloca
      (id0, t0, v, al)
  | LLVMsyntax.Coq_insn_load (i, t0, v, al) -> LLVMsyntax.Coq_insn_load (id0,
      t0, v, al)
  | LLVMsyntax.Coq_insn_store (i, t1, v1, v2, al) ->
      LLVMsyntax.Coq_insn_store (id0, t1, v1, v2, al)
  | LLVMsyntax.Coq_insn_gep (i, ib0, t0, v, vs) -> LLVMsyntax.Coq_insn_gep
      (id0, ib0, t0, v, vs)
  | LLVMsyntax.Coq_insn_trunc (i, top0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_trunc (id0, top0, t1, v1, t2)
  | LLVMsyntax.Coq_insn_ext (i, eop0, t1, v1, t2) -> LLVMsyntax.Coq_insn_ext
      (id0, eop0, t1, v1, t2)
  | LLVMsyntax.Coq_insn_cast (i, cop0, t1, v1, t2) ->
      LLVMsyntax.Coq_insn_cast (id0, cop0, t1, v1, t2)
  | LLVMsyntax.Coq_insn_icmp (i, t0, cond0, v1, v2) ->
      LLVMsyntax.Coq_insn_icmp (id0, t0, cond0, v1, v2)
  | LLVMsyntax.Coq_insn_fcmp (i, fcond0, fp0, v1, v2) ->
      LLVMsyntax.Coq_insn_fcmp (id0, fcond0, fp0, v1, v2)
  | LLVMsyntax.Coq_insn_select (i, v0, t0, v1, v2) ->
      LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2)
  | LLVMsyntax.Coq_insn_call (i, noret0, cl0, t1, v1, ps) ->
      LLVMsyntax.Coq_insn_call (id0, noret0, cl0, t1, v1, ps)

(** val motion_block :
    LLVMsyntax.l -> nat -> LLVMsyntax.id -> LLVMsyntax.cmd ->
    LLVMsyntax.block -> LLVMsyntax.block **)

let motion_block l1 n newid c b =
  let b1 = insert_block l1 n (gen_fresh_cmd newid c) b in
  let b2 = isubst_block (LLVMinfra.getCmdLoc c) newid b1 in
  let b3 = remove_block (LLVMinfra.getCmdLoc c) b2 in
  rename_block newid (LLVMinfra.getCmdLoc c) b3

(** val motion_fdef :
    LLVMsyntax.l -> nat -> LLVMsyntax.cmd -> LLVMsyntax.fdef ->
    LLVMsyntax.fdef **)

let motion_fdef l1 n c f = match f with
  | LLVMsyntax.Coq_fdef_intro (fh, bs) ->
      let newid = AtomImpl.atom_fresh_for_list (LLVMinfra.getBlocksLocs bs)
      in
      let f1 = insert_fdef l1 n (gen_fresh_cmd newid c) f in
      let f2 = isubst_fdef (LLVMinfra.getCmdLoc c) newid f1 in
      let f3 = remove_fdef (LLVMinfra.getCmdLoc c) f2 in
      rename_fdef newid (LLVMinfra.getCmdLoc c) f3

(** val print_reachablity : LLVMsyntax.l list -> bool **)

let print_reachablity = Transforms_aux.print_reachablity

(** val print_dominators :
    AtomImpl.atom set -> Dominators.t AMap.t -> bool **)

let print_dominators = Transforms_aux.print_dominators

(** val print_dtree : coq_DTree -> bool **)

let print_dtree = Transforms_aux.print_dtree

type coq_TNAME = int

(** val init_expected_name : unit -> coq_TNAME **)

let init_expected_name = Transforms_aux.init_expected_name

(** val check_bname :
    LLVMsyntax.l -> coq_TNAME -> (LLVMsyntax.l*coq_TNAME) option **)

let check_bname = Transforms_aux.check_bname

(** val check_vname :
    LLVMsyntax.id -> coq_TNAME -> (LLVMsyntax.id*coq_TNAME) option **)

let check_vname = Transforms_aux.check_vname

(** val renamel_list_value_l :
    LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.list_value_l ->
    LLVMsyntax.list_value_l **)

let rec renamel_list_value_l l1 l2 = function
  | LLVMsyntax.Nil_list_value_l -> LLVMsyntax.Nil_list_value_l
  | LLVMsyntax.Cons_list_value_l (v0, l3, tl) -> LLVMsyntax.Cons_list_value_l
      (v0, (rename_id l1 l2 l3), (renamel_list_value_l l1 l2 tl))

(** val renamel_phi :
    LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.phinode -> LLVMsyntax.phinode **)

let renamel_phi l1 l2 = function
  | LLVMsyntax.Coq_insn_phi (id0, t0, vls) -> LLVMsyntax.Coq_insn_phi (id0,
      t0, (renamel_list_value_l l1 l2 vls))

(** val renamel_block :
    LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.block **)

let renamel_block l1 l2 = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro ((rename_id l1 l2 l0),
      (map (renamel_phi l1 l2) ps0), cs0, tmn0)

(** val renamel_fdef :
    LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let renamel_fdef l1 l2 = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
      (map (renamel_block l1 l2) bs))

(** val fix_temporary_block :
    LLVMsyntax.fdef -> LLVMsyntax.block -> coq_TNAME ->
    (LLVMsyntax.fdef*coq_TNAME) option **)

let fix_temporary_block f b eid =
  let LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) = b in
  (match check_bname l0 eid with
     | Some p ->
         let l0',eid5 = p in
         let st =
           fold_left (fun st p0 ->
             match st with
               | Some y ->
                   let f0,eid0 = y in
                   (match check_vname (LLVMinfra.getPhiNodeID p0) eid0 with
                      | Some p1 ->
                          let pid',eid' = p1 in
                          if LLVMinfra.id_dec (LLVMinfra.getPhiNodeID p0)
                               pid'
                          then Some (f0,eid')
                          else Some
                                 ((rename_fdef (LLVMinfra.getPhiNodeID p0)
                                    pid' f0),eid')
                      | None -> None)
               | None -> None) ps (Some ((renamel_fdef l0 l0' f),eid5))
         in
         fold_left (fun st0 c ->
           match st0 with
             | Some y ->
                 let f0,eid0 = y in
                 (match LLVMinfra.getCmdID c with
                    | Some cid ->
                        (match check_vname cid eid0 with
                           | Some p0 ->
                               let cid',eid' = p0 in
                               if LLVMinfra.id_dec cid cid'
                               then Some (f0,eid')
                               else Some ((rename_fdef cid cid' f0),eid')
                           | None -> None)
                    | None -> Some (f0,eid0))
             | None -> None) cs st
     | None -> None)

(** val fix_temporary_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef option **)

let fix_temporary_fdef f =
  let eid = init_expected_name () in
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  (match fold_left (fun st b ->
           match st with
             | Some y -> let f0,eid0 = y in fix_temporary_block f0 b eid0
             | None -> None) bs (Some (f,eid)) with
     | Some p -> let f',t0 = p in Some f'
     | None -> None)

(** val getFdefLocs : LLVMsyntax.fdef -> LLVMsyntax.ids **)

let getFdefLocs = function
  | LLVMsyntax.Coq_fdef_intro (f, bs) ->
      let LLVMsyntax.Coq_fheader_intro (f0, t0, i, la, v) = f in
      app (LLVMinfra.getArgsIDs la) (LLVMinfra.getBlocksLocs bs)

