open Bool
open CoqEqDec
open Datatypes
open EqNat
open List0
open Metatheory
open MetatheoryAtom
open Peano
open Alist
open Infrastructure
open Sub_symexe
open Sub_tv_def
open Syntax

(** val is_hashLoadBaseBound : LLVMsyntax.id -> bool **)

let is_hashLoadBaseBound = Symexe_aux.is_hashLoadBaseBound

(** val is_loadStoreDereferenceCheck : LLVMsyntax.id -> bool **)

let is_loadStoreDereferenceCheck = Symexe_aux.is_loadStoreDereferenceCheck

(** val is_callDereferenceCheck : LLVMsyntax.id -> bool **)

let is_callDereferenceCheck = Symexe_aux.is_callDereferenceCheck

(** val is_hashStoreBaseBound : LLVMsyntax.id -> bool **)

let is_hashStoreBaseBound = Symexe_aux.is_hashStoreBaseBound

(** val remove_cast_const : LLVMsyntax.const -> LLVMsyntax.const **)

let rec remove_cast_const c = match c with
  | LLVMsyntax.Coq_const_castop (c0, c1, t) ->
      (match c0 with
         | LLVMsyntax.Coq_castop_bitcast -> remove_cast_const c1
         | _ -> c)
  | LLVMsyntax.Coq_const_select (c0, c1, c2) -> LLVMsyntax.Coq_const_select
      (c0, (remove_cast_const c1), (remove_cast_const c2))
  | _ -> c

(** val remove_cast : SBSE.sterm -> SBSE.sterm **)

let rec remove_cast st = match st with
  | SBSE.Coq_sterm_val v ->
      (match v with
         | LLVMsyntax.Coq_value_id i -> st
         | LLVMsyntax.Coq_value_const c -> SBSE.Coq_sterm_val
             (LLVMsyntax.Coq_value_const (remove_cast_const c)))
  | SBSE.Coq_sterm_cast (c, t, st1, t0) ->
      (match c with
         | LLVMsyntax.Coq_castop_bitcast -> remove_cast st1
         | _ -> st)
  | SBSE.Coq_sterm_select (st0, t, st1, st2) -> SBSE.Coq_sterm_select (st0,
      t, (remove_cast st1), (remove_cast st2))
  | _ -> st

(** val get_ptr_object_const : LLVMsyntax.const -> LLVMsyntax.const **)

let rec get_ptr_object_const c = match c with
  | LLVMsyntax.Coq_const_castop (c0, c1, t) ->
      (match c0 with
         | LLVMsyntax.Coq_castop_bitcast -> get_ptr_object_const c1
         | _ -> c)
  | LLVMsyntax.Coq_const_gep (i, c1, l0) -> get_ptr_object_const c1
  | LLVMsyntax.Coq_const_select (c0, c1, c2) -> LLVMsyntax.Coq_const_select
      (c0, (remove_cast_const c1), (remove_cast_const c2))
  | _ -> c

(** val get_ptr_object : SBSE.sterm -> SBSE.sterm **)

let rec get_ptr_object st = match st with
  | SBSE.Coq_sterm_val v ->
      (match v with
         | LLVMsyntax.Coq_value_id i -> st
         | LLVMsyntax.Coq_value_const c -> SBSE.Coq_sterm_val
             (LLVMsyntax.Coq_value_const (get_ptr_object_const c)))
  | SBSE.Coq_sterm_gep (i, t, st1, l0) -> get_ptr_object st1
  | SBSE.Coq_sterm_cast (c, t, st1, t0) ->
      (match c with
         | LLVMsyntax.Coq_castop_bitcast -> get_ptr_object st1
         | _ -> st)
  | SBSE.Coq_sterm_select (st0, t, st1, st2) -> SBSE.Coq_sterm_select (st0,
      t, (get_ptr_object st1), (get_ptr_object st2))
  | _ -> st

(** val eq_sterm_upto_cast : SBSE.sterm -> SBSE.sterm -> bool **)

let eq_sterm_upto_cast st1 st2 =
  eq_sterm (remove_cast st1) (remove_cast st2)

(** val l_of_arg : unit -> LLVMsyntax.l **)

let l_of_arg = Symexe_aux.l_of_arg

type beps = (((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id)*bool) list

type nbeps = (nat*beps) list

type lnbeps = (LLVMsyntax.l*nbeps) list

type flnbeps = (LLVMsyntax.id*lnbeps) list

(** val add_bep :
    beps -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool -> beps **)

let rec add_bep md b e p im =
  match md with
    | [] -> EnvImpl.one (((b,e),p),im)
    | p0::md' ->
        let p1,im' = p0 in
        let p2,p' = p1 in
        let b',e' = p2 in
        if if if if eq_id b b' then eq_id e e' else false
              then eq_id p p'
              else false
           then eqb im im'
           else false
        then md
        else (((b',e'),p'),im')::(add_bep md' b e p im)

(** val add_beps : beps -> beps -> beps **)

let rec add_beps accum = function
  | [] -> accum
  | p0::bep' ->
      let p1,im = p0 in
      let p2,p = p1 in let b,e = p2 in add_beps (add_bep accum b e p im) bep'

(** val updateAdd_nbeps : nbeps -> nat -> beps -> nbeps **)

let rec updateAdd_nbeps m i gv =
  match m with
    | [] -> (i,gv)::[]
    | p::m' ->
        let i',gv' = p in
        if beq_nat i i'
        then (i',gv)::m'
        else (i',gv')::(updateAdd_nbeps m' i gv)

(** val update_nbeps : nbeps -> nat -> beps -> nbeps **)

let rec update_nbeps m i gv =
  match m with
    | [] -> []
    | p::m' ->
        let i',gv' = p in
        if beq_nat i i'
        then (i',gv)::m'
        else (i',gv')::(update_nbeps m' i gv)

(** val lookup_nbeps : nbeps -> nat -> beps option **)

let rec lookup_nbeps m i =
  match m with
    | [] -> None
    | p::m' ->
        let i',gv' = p in
        if beq_nat i i' then Some gv' else lookup_nbeps m' i

(** val metadata_from_bep_aux :
    SBSE.sterm -> SBSE.sterm -> SBSE.sterm -> bool -> beps -> beps **)

let rec metadata_from_bep_aux base bound ptr im accum =
  let p0 = base,bound in
  let s,s0 = p0 in
  (match s with
     | SBSE.Coq_sterm_val v ->
         (match v with
            | LLVMsyntax.Coq_value_id b ->
                (match s0 with
                   | SBSE.Coq_sterm_val v0 ->
                       (match v0 with
                          | LLVMsyntax.Coq_value_id e ->
                              (match ptr with
                                 | SBSE.Coq_sterm_val v1 ->
                                     (match v1 with
                                        | LLVMsyntax.Coq_value_id p ->
                                            add_bep accum b e p im
                                        | LLVMsyntax.Coq_value_const c ->
                                            accum)
                                 | _ -> accum)
                          | LLVMsyntax.Coq_value_const c -> accum)
                   | _ -> accum)
            | LLVMsyntax.Coq_value_const c -> accum)
     | SBSE.Coq_sterm_select (st10, t, st11, st12) ->
         (match s0 with
            | SBSE.Coq_sterm_select (st20, t0, st21, st22) ->
                (match ptr with
                   | SBSE.Coq_sterm_select (st30, t1, st31, st32) ->
                       if if eq_sterm st10 st20
                          then eq_sterm st20 st30
                          else false
                       then metadata_from_bep_aux st11 st21 st31 im
                              (metadata_from_bep_aux st12 st22 st32 im accum)
                       else accum
                   | _ -> accum)
            | _ -> accum)
     | _ -> accum)

(** val metadata_from_bep :
    SBSE.sterm -> SBSE.sterm -> SBSE.sterm -> bool -> beps -> beps **)

let metadata_from_bep base bound ptr im accum =
  metadata_from_bep_aux (remove_cast base) (remove_cast bound)
    (get_ptr_object ptr) im accum

(** val metadata_from_smem : SBSE.smem -> beps -> beps **)

let rec metadata_from_smem sm accum =
  match sm with
    | SBSE.Coq_smem_init -> accum
    | SBSE.Coq_smem_malloc (sm1, t, s, a) -> metadata_from_smem sm1 accum
    | SBSE.Coq_smem_free (sm1, t, s) -> metadata_from_smem sm1 accum
    | SBSE.Coq_smem_alloca (sm1, t, s, a) -> metadata_from_smem sm1 accum
    | SBSE.Coq_smem_load (sm1, t, s, a) -> metadata_from_smem sm1 accum
    | SBSE.Coq_smem_store (sm1, t, s, s0, a) -> metadata_from_smem sm1 accum
    | SBSE.Coq_smem_lib (sm1, lid1, sts1) ->
        metadata_from_smem sm1
          (if is_loadStoreDereferenceCheck lid1
           then (match sts1 with
                   | SBSE.Nil_list_sterm -> accum
                   | SBSE.Cons_list_sterm (base, l0) ->
                       (match l0 with
                          | SBSE.Nil_list_sterm -> accum
                          | SBSE.Cons_list_sterm (bound, l1) ->
                              (match l1 with
                                 | SBSE.Nil_list_sterm -> accum
                                 | SBSE.Cons_list_sterm (
                                     ptr, l2) ->
                                     (match l2 with
                                        | SBSE.Nil_list_sterm -> accum
                                        | SBSE.Cons_list_sterm (
                                            s, l3) ->
                                            (match l3 with
                                               | SBSE.Nil_list_sterm -> accum
                                               | SBSE.Cons_list_sterm
                                                  (s0, l4) ->
                                                  (match l4 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  metadata_from_bep base
                                                  bound ptr true accum
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s1, l5) -> accum))))))
           else if is_callDereferenceCheck lid1
                then (match sts1 with
                        | SBSE.Nil_list_sterm -> accum
                        | SBSE.Cons_list_sterm (base, l0) ->
                            (match l0 with
                               | SBSE.Nil_list_sterm -> accum
                               | SBSE.Cons_list_sterm (
                                   bound, l1) ->
                                   (match l1 with
                                      | SBSE.Nil_list_sterm -> accum
                                      | SBSE.Cons_list_sterm (
                                          ptr, l2) ->
                                          (match l2 with
                                             | SBSE.Nil_list_sterm ->
                                                 metadata_from_bep base bound
                                                  ptr false accum
                                             | SBSE.Cons_list_sterm
                                                 (s, l3) -> accum))))
                else accum)

(** val metadata_from_sterms_aux : SBSE.smap -> beps -> beps -> beps **)

let rec metadata_from_sterms_aux sm accum = function
  | [] -> accum
  | p0::md' ->
      let p1,im = p0 in
      let p2,p = p1 in
      let b,e = p2 in
      metadata_from_sterms_aux sm
        (let p3 = (lookupAL sm b),(lookupAL sm e) in
        let o = lookupAL sm p in
        let o0,o1 = p3 in
        (match o0 with
           | Some sb ->
               (match o1 with
                  | Some se ->
                      (match o with
                         | Some sp -> metadata_from_bep sb se sp im accum
                         | None ->
                             let s = remove_cast sb in
                             let s0 = remove_cast se in
                             (match s with
                                | SBSE.Coq_sterm_val v ->
                                    (match v with
                                       | LLVMsyntax.Coq_value_id b' ->
                                           (match s0 with
                                              | SBSE.Coq_sterm_val v0 ->
                                                  (
                                                  match v0 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  e' ->
                                                  add_bep accum b' e' p im
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> accum)
                                              | _ -> accum)
                                       | LLVMsyntax.Coq_value_const c ->
                                           accum)
                                | _ -> accum))
                  | None -> accum)
           | None ->
               (match o1 with
                  | Some s -> accum
                  | None ->
                      (match o with
                         | Some sp ->
                             (match get_ptr_object sp with
                                | SBSE.Coq_sterm_val v ->
                                    (match v with
                                       | LLVMsyntax.Coq_value_id p' ->
                                           add_bep accum b e p' im
                                       | LLVMsyntax.Coq_value_const c ->
                                           accum)
                                | _ -> accum)
                         | None -> accum)))) md'

(** val metadata_from_sterms : SBSE.smap -> beps -> beps **)

let rec metadata_from_sterms sm accum =
  metadata_from_sterms_aux sm accum accum

(** val metadata_from_cmds : SBSE.nbranch list -> beps -> beps **)

let metadata_from_cmds nbs2 accum =
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  let accum' = metadata_from_smem st2.SBSE.coq_SMem accum in
  metadata_from_sterms st2.SBSE.coq_STerms accum'

(** val lookupSarg :
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id) list ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
    -> SBSE.sterm option **)

let rec lookupSarg ars2 sars2 i =
  match ars2 with
    | [] -> None
    | p::ars2' ->
        let p0,i' = p in
        (match sars2 with
           | [] -> None
           | p1::sars2' ->
               let p2,s' = p1 in
               if eq_id i i' then Some s' else lookupSarg ars2' sars2' i)

(** val metadata_from_params :
    beps -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id) list ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> beps -> beps **)

let rec metadata_from_params ar_bep ars2 sars2 accum =
  match ar_bep with
    | [] -> accum
    | p0::ar_bep' ->
        let p1,im = p0 in
        let p2,p = p1 in
        let b,e = p2 in
        metadata_from_params ar_bep' ars2 sars2
          (let p3 = (lookupSarg ars2 sars2 b),(lookupSarg ars2 sars2 e) in
          let o = lookupSarg ars2 sars2 p in
          let o0,o1 = p3 in
          (match o0 with
             | Some sb ->
                 (match o1 with
                    | Some se ->
                        (match o with
                           | Some sp -> metadata_from_bep sb se sp im accum
                           | None -> accum)
                    | None -> accum)
             | None -> accum))

(** val get_arg_metadata : flnbeps -> AtomImpl.atom -> beps **)

let get_arg_metadata md fid =
  match lookupAL md fid with
    | Some lnbeps0 ->
        (match lookupAL lnbeps0 (l_of_arg ()) with
           | Some nbeps0 ->
               (match lookup_nbeps nbeps0 O with
                  | Some beps0 -> beps0
                  | None -> [])
           | None -> [])
    | None -> []

type sicall =
  | Coq_stmn_icall_nptr of LLVMsyntax.id * LLVMsyntax.noret
     * LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
  | Coq_stmn_icall_ptr of LLVMsyntax.id * LLVMsyntax.noret
     * LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list
     * LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
     LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
     LLVMsyntax.id * LLVMsyntax.const * LLVMsyntax.const * 
     LLVMsyntax.const

(** val sicall_rect :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> 'a1) ->
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
    -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.const -> 'a1) -> sicall -> 'a1 **)

let sicall_rect f f0 = function
  | Coq_stmn_icall_nptr (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  | Coq_stmn_icall_ptr
      (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
      f0 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14

(** val sicall_rec :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> 'a1) ->
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> LLVMsyntax.id
    -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const ->
    LLVMsyntax.const -> 'a1) -> sicall -> 'a1 **)

let sicall_rec f f0 = function
  | Coq_stmn_icall_nptr (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  | Coq_stmn_icall_ptr
      (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
      f0 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14

(** val se_icall : SBSE.sstate -> SBsyntax.call -> sicall **)

let se_icall st = function
  | SBsyntax.Coq_insn_call_nptr (id0, nr, ca, t0, v0, p0) ->
      Coq_stmn_icall_nptr (id0, nr, ca, t0,
      (SBSE.value2Sterm st.SBSE.coq_STerms v0),
      (SBSE.list_param__list_typ_subst_sterm p0 st.SBSE.coq_STerms))
  | SBsyntax.Coq_insn_call_ptr
      (id0, nr, ca, t0, v0, p0, sid, id1, id2, id3, id4, id5, id6, cst0,
       cst1, cts2) -> Coq_stmn_icall_ptr (id0, nr, ca, t0,
      (SBSE.value2Sterm st.SBSE.coq_STerms v0),
      (SBSE.list_param__list_typ_subst_sterm p0 st.SBSE.coq_STerms), sid,
      id1, id2, id3, id4, id5, id6, cst0, cst1, cts2)

(** val metadata_from_iscall :
    SBsyntax.products -> flnbeps -> beps -> sicall -> beps **)

let metadata_from_iscall ps2 flnbep0 accum = function
  | Coq_stmn_icall_nptr (i, n, c, t, t2, tsts2) ->
      (match remove_cast t2 with
         | SBSE.Coq_sterm_val v ->
             (match v with
                | LLVMsyntax.Coq_value_id i0 -> accum
                | LLVMsyntax.Coq_value_const c0 ->
                    (match c0 with
                       | LLVMsyntax.Coq_const_gid (
                           t0, fid2) ->
                           if SBSE.isCallLib fid2
                           then accum
                           else (match SBsyntax.lookupFdefViaIDFromProducts
                                         ps2 fid2 with
                                   | Some f ->
                                       let SBsyntax.Coq_fdef_intro (
                                         f0, b) = f
                                       in
                                       let LLVMsyntax.Coq_fheader_intro
                                         (f1, t1, i0, args2, v0) = f0
                                       in
                                       metadata_from_params
                                         (get_arg_metadata flnbep0 fid2)
                                         args2 tsts2 accum
                                   | None -> accum)
                       | _ -> accum))
         | _ -> accum)
  | Coq_stmn_icall_ptr
      (i, n, c, t, t2, tsts2, i0, i1, i2, i3, i4, i5, i6, c0, c1, c3) ->
      (match remove_cast t2 with
         | SBSE.Coq_sterm_val v ->
             (match v with
                | LLVMsyntax.Coq_value_id i7 -> accum
                | LLVMsyntax.Coq_value_const c4 ->
                    (match c4 with
                       | LLVMsyntax.Coq_const_gid (
                           t0, fid2) ->
                           if SBSE.isCallLib fid2
                           then accum
                           else (match SBsyntax.lookupFdefViaIDFromProducts
                                         ps2 fid2 with
                                   | Some f ->
                                       let SBsyntax.Coq_fdef_intro (
                                         f0, b) = f
                                       in
                                       let LLVMsyntax.Coq_fheader_intro
                                         (f1, t1, i7, a, v0) = f0
                                       in
                                       (match a with
                                          | [] -> accum
                                          | p::args2 ->
                                              metadata_from_params
                                                (get_arg_metadata flnbep0
                                                  fid2) args2 tsts2 accum)
                                   | None -> accum)
                       | _ -> accum))
         | _ -> accum)

(** val metadata_from_subblock :
    SBsyntax.products -> flnbeps -> SBsyntax.subblock -> beps -> beps **)

let metadata_from_subblock ps2 flnbep sb2 accum =
  let { SBsyntax.coq_NBs = nbs2; SBsyntax.call_cmd = call2 } = sb2 in
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  let cl2 = se_icall st2 call2 in
  let accum' = metadata_from_iscall ps2 flnbep accum cl2 in
  let accum'' = metadata_from_sterms st2.SBSE.coq_STerms accum' in
  metadata_from_smem st2.SBSE.coq_SMem accum''

(** val metadata_diff_cmds : beps -> LLVMsyntax.cmds -> beps **)

let rec metadata_diff_cmds md cs2 =
  match md with
    | [] -> md
    | p0::md' ->
        let p1,im = p0 in
        let p2,p = p1 in
        (match LLVMinfra.lookupCmdViaIDFromCmds cs2 p with
           | Some c -> metadata_diff_cmds md' cs2
           | None -> ((p2,p),im)::(metadata_diff_cmds md' cs2))

(** val update_pred_subblock : nbeps -> nat -> beps -> nbeps **)

let update_pred_subblock accum nth bep =
  let bep_nth =
    match lookup_nbeps accum (S nth) with
      | Some bep_nth -> bep_nth
      | None -> []
  in
  updateAdd_nbeps accum (S nth) (add_beps bep_nth bep)

(** val metadata_from_subblocks_aux :
    SBsyntax.products -> flnbeps -> nat -> SBsyntax.subblock list -> nbeps ->
    nbeps **)

let rec metadata_from_subblocks_aux ps2 flnbep len sbs2 accum =
  match sbs2 with
    | [] -> accum
    | sb2::sbs2' ->
        let nth = length sbs2' in
        let bep =
          match lookup_nbeps accum nth with
            | Some bep -> bep
            | None -> []
        in
        let bep' = metadata_from_subblock ps2 flnbep sb2 bep in
        let accum' = update_nbeps accum (minus len nth) bep' in
        let accum'' =
          update_pred_subblock accum' nth
            (metadata_diff_cmds bep'
              (SBSE.nbranchs2cmds sb2.SBsyntax.coq_NBs))
        in
        metadata_from_subblocks_aux ps2 flnbep len sbs2' accum''

(** val metadata_from_subblocks :
    SBsyntax.products -> flnbeps -> SBsyntax.subblock list -> nbeps -> nbeps **)

let metadata_from_subblocks ps2 flnbep sbs2 accum =
  metadata_from_subblocks_aux ps2 flnbep (length sbs2) (rev sbs2) accum

(** val lookupPhinode :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.phinode option **)

let rec lookupPhinode phs i =
  match phs with
    | [] -> None
    | p::phs' ->
        let LLVMsyntax.Coq_insn_phi (i', t, vs) = p in
        if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i i'
        then Some (LLVMsyntax.Coq_insn_phi (i', t, vs))
        else lookupPhinode phs' i

(** val update_block_metadata : lnbeps -> LLVMsyntax.l -> beps -> lnbeps **)

let update_block_metadata accum l1 md0 =
  let nbep = match lookupAL accum l1 with
               | Some nbep -> nbep
               | None -> []
  in
  let bep = match lookup_nbeps nbep O with
              | Some bep -> bep
              | None -> []
  in
  let bep' = add_beps bep md0 in
  let nbep' = updateAdd_nbeps nbep O bep' in updateAL accum l1 nbep'

(** val metadata_from_value :
    LLVMsyntax.l -> LLVMsyntax.value -> LLVMsyntax.value -> LLVMsyntax.value
    -> bool -> lnbeps -> lnbeps **)

let metadata_from_value l1 bv ev pv im accum =
  let p = bv,ev in
  let v,v0 = p in
  (match v with
     | LLVMsyntax.Coq_value_id bid ->
         (match v0 with
            | LLVMsyntax.Coq_value_id eid ->
                (match pv with
                   | LLVMsyntax.Coq_value_id pid ->
                       update_block_metadata accum l1
                         (EnvImpl.one (((bid,eid),pid),im))
                   | LLVMsyntax.Coq_value_const c -> accum)
            | LLVMsyntax.Coq_value_const c -> accum)
     | LLVMsyntax.Coq_value_const c -> accum)

(** val metadata_from_list_value_l :
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l ->
    LLVMsyntax.list_value_l -> bool -> lnbeps -> lnbeps **)

let rec metadata_from_list_value_l bvls evls pvls im accum =
  match bvls with
    | LLVMsyntax.Nil_list_value_l -> accum
    | LLVMsyntax.Cons_list_value_l (bv, bl, bvls') ->
        metadata_from_list_value_l bvls' evls pvls im
          (let o = LLVMinfra.getValueViaLabelFromValuels evls bl in
          let o0 = LLVMinfra.getValueViaLabelFromValuels pvls bl in
          (match o with
             | Some ev ->
                 (match o0 with
                    | Some pv -> metadata_from_value bl bv ev pv im accum
                    | None -> accum)
             | None -> accum))

(** val metadata_from_phinodes :
    LLVMsyntax.phinodes -> lnbeps -> beps -> lnbeps **)

let rec metadata_from_phinodes ps2 accum = function
  | [] -> accum
  | p0::md' ->
      let p1,im = p0 in
      let p2,p = p1 in
      let b,e = p2 in
      metadata_from_phinodes ps2
        (let p3 = (lookupPhinode ps2 b),(lookupPhinode ps2 e) in
        let o = lookupPhinode ps2 p in
        let o0,o1 = p3 in
        (match o0 with
           | Some p4 ->
               let LLVMsyntax.Coq_insn_phi (i, t, bvls) = p4 in
               (match o1 with
                  | Some p5 ->
                      let LLVMsyntax.Coq_insn_phi (i0, t0, evls) = p5 in
                      (match o with
                         | Some p6 ->
                             let LLVMsyntax.Coq_insn_phi (i1, t1, pvls) = p6
                             in
                             metadata_from_list_value_l bvls evls pvls im
                               accum
                         | None -> accum)
                  | None -> accum)
           | None -> accum)) md'

(** val updatePredBlocks : LLVMsyntax.l list -> lnbeps -> beps -> lnbeps **)

let rec updatePredBlocks ls accum md0 =
  match ls with
    | [] -> accum
    | l1::ls' ->
        updatePredBlocks ls' (update_block_metadata accum l1 md0) md0

(** val metadata_diff_phinodes : beps -> LLVMsyntax.phinodes -> beps **)

let rec metadata_diff_phinodes md ps2 =
  match md with
    | [] -> md
    | p0::md' ->
        let p1,im = p0 in
        let p2,p = p1 in
        let b,e = p2 in
        (match lookupPhinode ps2 b with
           | Some p3 -> metadata_diff_phinodes md' ps2
           | None -> (((b,e),p),im)::(metadata_diff_phinodes md' ps2))

type usedef_block = (LLVMsyntax.l*LLVMsyntax.l list) list

(** val update_udb :
    usedef_block -> LLVMsyntax.l -> LLVMsyntax.l -> usedef_block **)

let update_udb udb lu ld =
  let ls = match lookupAL udb ld with
             | Some ls -> ls
             | None -> [] in
  if in_dec LLVMinfra.l_dec lu ls then udb else updateAddAL udb ld (lu::ls)

(** val genBlockUseDef_block :
    SBsyntax.block -> usedef_block -> usedef_block **)

let genBlockUseDef_block b udb =
  match b with
    | SBsyntax.Coq_block_common (l0, p, l1, l2, tmn2) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br (i, v, l3, l4) ->
               update_udb (update_udb udb l0 l4) l0 l3
           | LLVMsyntax.Coq_insn_br_uncond (i, l3) -> update_udb udb l0 l3
           | _ -> udb)
    | SBsyntax.Coq_block_ret_ptr (l0, p, l1, l2, i) -> udb

(** val genBlockUseDef_blocks :
    SBsyntax.block list -> usedef_block -> usedef_block **)

let rec genBlockUseDef_blocks bs udb =
  match bs with
    | [] -> udb
    | b::bs' -> genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)

(** val genBlockUseDef_fdef : SBsyntax.fdef -> usedef_block **)

let genBlockUseDef_fdef = function
  | SBsyntax.Coq_fdef_intro (f, lb2) -> genBlockUseDef_blocks lb2 []

(** val metadata_from_block_aux :
    SBsyntax.products -> flnbeps -> (nat*beps) list coq_AssocList ->
    AtomImpl.atom -> LLVMsyntax.phinodes -> SBsyntax.subblock list ->
    SBSE.nbranch list -> LLVMsyntax.l list coq_AssocList -> lnbeps **)

let metadata_from_block_aux ps2 flnbep lnbep l2 ps3 sbs2 nbs2 udb =
  let nbep0 = match lookupAL lnbep l2 with
                | Some nbep -> nbep
                | None -> []
  in
  let bep0 = match lookup_nbeps nbep0 O with
               | Some bep -> bep
               | None -> []
  in
  let bep1 = metadata_from_cmds nbs2 bep0 in
  let nbep1 = updateAdd_nbeps nbep0 O bep1 in
  let nbep2 =
    update_pred_subblock nbep1 O
      (metadata_diff_cmds bep1 (SBSE.nbranchs2cmds nbs2))
  in
  let nbep3 = metadata_from_subblocks ps2 flnbep sbs2 nbep2 in
  let lnbep' = updateAddAL lnbep l2 nbep3 in
  let bep_phi =
    match lookup_nbeps nbep3 (plus (length sbs2) (S O)) with
      | Some bep -> bep
      | None -> []
  in
  let lnbep'' = metadata_from_phinodes ps3 lnbep' bep_phi in
  let preds = match lookupAL udb l2 with
                | Some ls -> ls
                | None -> [] in
  updatePredBlocks preds lnbep'' (metadata_diff_phinodes bep_phi ps3)

(** val metadata_from_block :
    SBsyntax.products -> flnbeps -> SBsyntax.block -> usedef_block -> lnbeps
    -> lnbeps **)

let metadata_from_block ps2 flnbep b2 udb lnbep =
  match b2 with
    | SBsyntax.Coq_block_common (l2, ps3, sbs2, nbs2, tmn2) ->
        metadata_from_block_aux ps2 flnbep lnbep l2 ps3 sbs2 nbs2 udb
    | SBsyntax.Coq_block_ret_ptr (l2, ps3, sbs2, nbs2, i) ->
        let SBsyntax.Coq_insn_return_ptr
          (i0, t, i1, i2, i3, vb, i4, i5, ve, i6, vp, i7, c, c0, c1) = i
        in
        let lnbep0 = metadata_from_value l2 vb ve vp true lnbep in
        metadata_from_block_aux ps2 flnbep lnbep0 l2 ps3 sbs2 nbs2 udb

(** val metadata_from_blocks_aux :
    SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
    -> lnbeps **)

let rec metadata_from_blocks_aux ps2 flnbep bs2 udb lnbep =
  match bs2 with
    | [] -> lnbep
    | b2::bs2' ->
        metadata_from_blocks_aux ps2 flnbep bs2' udb
          (metadata_from_block ps2 flnbep b2 udb lnbep)

(** val eq_nbeps : nbeps -> nbeps -> bool **)

let rec eq_nbeps md1 md2 =
  match md1 with
    | [] -> (match md2 with
               | [] -> true
               | p::l0 -> false)
    | p::md1' ->
        let n1,bep1 = p in
        (match md2 with
           | [] -> false
           | p0::md2' ->
               let n2,bep2 = p0 in
               if if beq_nat n1 n2
                  then beq_nat (length bep1) (length bep2)
                  else false
               then eq_nbeps md1' md2'
               else false)

(** val eq_lnbeps : lnbeps -> lnbeps -> bool **)

let rec eq_lnbeps md1 md2 =
  match md1 with
    | [] -> (match md2 with
               | [] -> true
               | p::l0 -> false)
    | p::md1' ->
        let l1,nbep1 = p in
        (match md2 with
           | [] -> false
           | p0::md2' ->
               let l2,nbep2 = p0 in
               if if eq_l l1 l2 then eq_nbeps nbep1 nbep2 else false
               then eq_lnbeps md1' md2'
               else false)

(** val onat_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

let rec onat_rect f f0 o =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> f)
    (fun o0 -> f0 o0 (onat_rect f f0 o0))
    o

(** val onat_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1 **)

let rec onat_rec f f0 o =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> f)
    (fun o0 -> f0 o0 (onat_rec f f0 o0))
    o

(** val metadata_from_blocks :
    SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
    -> int -> lnbeps **)

let rec metadata_from_blocks ps2 flbep bs2 udb md bsteps =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> md)
    (fun bsteps' ->
    let md' = metadata_from_blocks_aux ps2 flbep bs2 udb md in
    if eq_lnbeps md md'
    then md'
    else metadata_from_blocks ps2 flbep bs2 udb md' bsteps')
    bsteps

(** val metadata_from_args : LLVMsyntax.args -> beps -> beps -> beps **)

let rec metadata_from_args a md accum =
  match md with
    | [] -> accum
    | p0::md' ->
        let p1,im = p0 in
        let p2,p = p1 in
        let b,e = p2 in
        metadata_from_args a md'
          (let p3 =
             (LLVMinfra.lookupArgViaIDFromArgs a b),
             (LLVMinfra.lookupArgViaIDFromArgs a e)
           in
          let o = LLVMinfra.lookupArgViaIDFromArgs a p in
          let o0,o1 = p3 in
          (match o0 with
             | Some a0 ->
                 (match o1 with
                    | Some a1 ->
                        (match o with
                           | Some a2 -> add_bep accum b e p im
                           | None -> accum)
                    | None -> accum)
             | None -> accum))

(** val metadata_from_fdef :
    SBsyntax.products -> flnbeps -> SBsyntax.fdef -> lnbeps -> int -> lnbeps **)

let metadata_from_fdef ps2 flbep f2 md bsteps =
  let SBsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  let LLVMsyntax.Coq_fheader_intro (f, t2, fid2, a2, v) = fh2 in
  if SBSE.isCallLib fid2
  then md
  else let accum =
         metadata_from_blocks ps2 flbep lb2 (genBlockUseDef_fdef f2) md
           bsteps
       in
       (match SBsyntax.getEntryBlock f2 with
          | Some b ->
              (match b with
                 | SBsyntax.Coq_block_common (l2, p, l0, l1, t) ->
                     (match lookupAL accum l2 with
                        | Some nbep ->
                            (match lookup_nbeps nbep
                                     (minus (length nbep) (S O)) with
                               | Some bep ->
                                   updateAddAL accum 
                                     (l_of_arg ())
                                     (EnvImpl.one
                                       (O,(metadata_from_args a2 bep [])))
                               | None -> accum)
                        | None -> accum)
                 | SBsyntax.Coq_block_ret_ptr (l2, p, l0, l1, i) ->
                     (match lookupAL accum l2 with
                        | Some nbep ->
                            (match lookup_nbeps nbep
                                     (minus (length nbep) (S O)) with
                               | Some bep ->
                                   updateAddAL accum 
                                     (l_of_arg ())
                                     (EnvImpl.one
                                       (O,(metadata_from_args a2 bep [])))
                               | None -> accum)
                        | None -> accum))
          | None -> accum)

(** val metadata_from_products_aux :
    SBsyntax.products -> SBsyntax.products -> flnbeps -> int -> flnbeps **)

let rec metadata_from_products_aux ps20 ps2 md bsteps =
  match ps2 with
    | [] -> md
    | p::ps2' ->
        (match p with
           | SBsyntax.Coq_product_fdef f2 ->
               let lnbep0 =
                 match lookupAL md (SBsyntax.getFdefID f2) with
                   | Some md0 -> md0
                   | None -> []
               in
               let lnbep = metadata_from_fdef ps20 md f2 lnbep0 bsteps in
               let md' = updateAddAL md (SBsyntax.getFdefID f2) lnbep in
               metadata_from_products_aux ps20 ps2' md' bsteps
           | _ -> metadata_from_products_aux ps20 ps2' md bsteps)

(** val eq_flnbeps : flnbeps -> flnbeps -> bool **)

let rec eq_flnbeps md1 md2 =
  match md1 with
    | [] -> (match md2 with
               | [] -> true
               | p::l0 -> false)
    | p::md1' ->
        let f1,lnbeps1 = p in
        (match md2 with
           | [] -> false
           | p0::md2' ->
               let f2,lnbeps2 = p0 in
               if if eq_id f1 f2 then eq_lnbeps lnbeps1 lnbeps2 else false
               then eq_flnbeps md1' md2'
               else false)

(** val metadata_from_products :
    SBsyntax.products -> flnbeps -> int -> int -> flnbeps **)

let rec metadata_from_products ps2 md bsteps psteps =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> md)
    (fun psteps' ->
    let md' = metadata_from_products_aux ps2 ps2 md bsteps in
    if eq_flnbeps md md'
    then md'
    else metadata_from_products ps2 md' bsteps psteps')
    psteps

(** val metadata_from_module :
    SBsyntax.coq_module -> int -> int -> flnbeps **)

let metadata_from_module m2 bsteps psteps =
  let SBsyntax.Coq_module_intro (l0, n, ps2) = m2 in
  metadata_from_products ps2 [] bsteps psteps

(** val validate_metadata_from_blocks :
    SBsyntax.products -> flnbeps -> SBsyntax.blocks -> usedef_block -> lnbeps
    -> bool **)

let validate_metadata_from_blocks ps2 flbep bs2 udb md =
  let md' = metadata_from_blocks_aux ps2 flbep bs2 udb md in eq_lnbeps md md'

(** val nbeps_to_beps : nbeps -> beps -> beps **)

let rec nbeps_to_beps nbep accum =
  match nbep with
    | [] -> accum
    | p::nbep' -> let n,bep = p in app (nbeps_to_beps nbep' bep) accum

(** val lnbeps_to_nbeps : lnbeps -> nbeps -> nbeps **)

let rec lnbeps_to_nbeps lnbep accum =
  match lnbep with
    | [] -> accum
    | p::lnbep' -> let l0,nbep = p in app (lnbeps_to_nbeps lnbep' nbep) accum

(** val in_beps :
    beps -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool -> bool **)

let rec in_beps md b e p im =
  match md with
    | [] -> false
    | p0::md' ->
        let p1,im' = p0 in
        let p2,p' = p1 in
        let b',e' = p2 in
        if if if if eq_id b b' then eq_id e e' else false
              then eq_id p p'
              else false
           then eqb im im'
           else false
        then true
        else in_beps md' b e p im

(** val disjoint_mptr_fptr_metadata_aux : beps -> bool **)

let rec disjoint_mptr_fptr_metadata_aux = function
  | [] -> true
  | p0::bep' ->
      let p1,im = p0 in
      let p2,p = p1 in
      let b,e = p2 in
      if negb (in_beps bep' b e p (negb im))
      then disjoint_mptr_fptr_metadata_aux bep'
      else false

(** val disjoint_mptr_fptr_metadata : lnbeps -> bool **)

let disjoint_mptr_fptr_metadata md =
  disjoint_mptr_fptr_metadata_aux (nbeps_to_beps (lnbeps_to_nbeps md []) [])

(** val validate_metadata_from_fdef :
    SBsyntax.products -> flnbeps -> SBsyntax.fdef -> lnbeps -> bool **)

let validate_metadata_from_fdef ps2 flbep f2 md =
  let SBsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  let LLVMsyntax.Coq_fheader_intro (f, t2, fid2, a2, v) = fh2 in
  if SBSE.isCallLib fid2
  then true
  else if if disjoint_mptr_fptr_metadata md
          then validate_metadata_from_blocks ps2 flbep lb2
                 (genBlockUseDef_fdef f2) md
          else false
       then (match SBsyntax.getEntryBlock f2 with
               | Some b ->
                   (match b with
                      | SBsyntax.Coq_block_common (
                          l2, p, l0, l1, t) ->
                          (match lookupAL md l2 with
                             | Some nbep ->
                                 (match lookup_nbeps nbep
                                          (minus (length nbep) (S O)) with
                                    | Some bep ->
                                        (match lookupAL md (l_of_arg ()) with
                                           | Some nbep' ->
                                               eq_nbeps nbep'
                                                 (EnvImpl.one
                                                  (O,
                                                  (metadata_from_args a2 bep
                                                  [])))
                                           | None -> false)
                                    | None -> false)
                             | None -> false)
                      | SBsyntax.Coq_block_ret_ptr (
                          l2, p, l0, l1, i) ->
                          (match lookupAL md l2 with
                             | Some nbep ->
                                 (match lookup_nbeps nbep
                                          (minus (length nbep) (S O)) with
                                    | Some bep ->
                                        (match lookupAL md (l_of_arg ()) with
                                           | Some nbep' ->
                                               eq_nbeps nbep'
                                                 (EnvImpl.one
                                                  (O,
                                                  (metadata_from_args a2 bep
                                                  [])))
                                           | None -> false)
                                    | None -> false)
                             | None -> false))
               | None -> false)
       else false

(** val validate_metadata_from_products_aux :
    SBsyntax.products -> SBsyntax.products -> flnbeps -> bool **)

let rec validate_metadata_from_products_aux ps20 ps2 md =
  match ps2 with
    | [] -> true
    | p::ps2' ->
        (match p with
           | SBsyntax.Coq_product_fdef f2 ->
               (match lookupAL md (SBsyntax.getFdefID f2) with
                  | Some lnbep ->
                      if validate_metadata_from_fdef ps20 md f2 lnbep
                      then validate_metadata_from_products_aux ps20 ps2' md
                      else false
                  | None -> false)
           | _ -> validate_metadata_from_products_aux ps20 ps2' md)

(** val validate_metadata_from_module :
    SBsyntax.coq_module -> flnbeps -> bool **)

let validate_metadata_from_module m2 md =
  let SBsyntax.Coq_module_intro (l0, n, ps2) = m2 in
  validate_metadata_from_products_aux ps2 ps2 md

type abes = (LLVMsyntax.id*LLVMsyntax.id) list

(** val add_abes : abes -> LLVMsyntax.id -> LLVMsyntax.id -> abes **)

let rec add_abes md ab ae =
  match md with
    | [] -> EnvImpl.one (ab,ae)
    | p::md' ->
        let ab',ae' = p in
        if if eq_id ab ab' then eq_id ae ae' else false
        then md
        else (ab',ae')::(add_abes md' ab ae)

(** val addrofbe_from_smem : SBSE.smem -> abes -> abes **)

let rec addrofbe_from_smem sm accum =
  match sm with
    | SBSE.Coq_smem_init -> accum
    | SBSE.Coq_smem_malloc (sm1, t, s, a) -> addrofbe_from_smem sm1 accum
    | SBSE.Coq_smem_free (sm1, t, s) -> addrofbe_from_smem sm1 accum
    | SBSE.Coq_smem_alloca (sm1, t, s, a) -> addrofbe_from_smem sm1 accum
    | SBSE.Coq_smem_load (sm1, t, s, a) -> addrofbe_from_smem sm1 accum
    | SBSE.Coq_smem_store (sm1, t, s, s0, a) -> addrofbe_from_smem sm1 accum
    | SBSE.Coq_smem_lib (sm1, lid1, sts1) ->
        addrofbe_from_smem sm1
          (if is_hashLoadBaseBound lid1
           then (match sts1 with
                   | SBSE.Nil_list_sterm -> accum
                   | SBSE.Cons_list_sterm (s, l0) ->
                       (match l0 with
                          | SBSE.Nil_list_sterm -> accum
                          | SBSE.Cons_list_sterm (addr_of_base, l1) ->
                              (match l1 with
                                 | SBSE.Nil_list_sterm -> accum
                                 | SBSE.Cons_list_sterm
                                     (addr_of_bound, l2) ->
                                     (match l2 with
                                        | SBSE.Nil_list_sterm -> accum
                                        | SBSE.Cons_list_sterm (
                                            s0, l3) ->
                                            (match l3 with
                                               | SBSE.Nil_list_sterm -> accum
                                               | SBSE.Cons_list_sterm
                                                  (s1, l4) ->
                                                  (match l4 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  accum
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s2, l5) ->
                                                  (match l5 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  (match addr_of_base with
                                                    | 
                                                  SBSE.Coq_sterm_val v ->
                                                  (match v with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  ab ->
                                                  (match addr_of_bound with
                                                    | 
                                                  SBSE.Coq_sterm_val v0 ->
                                                  (match v0 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  ae -> 
                                                  add_abes accum ab ae
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> accum)
                                                    | 
                                                  _ -> accum)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> accum)
                                                    | 
                                                  _ -> accum)
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s3, l6) -> accum)))))))
           else accum)

(** val addrofbe_from_cmds : SBSE.nbranch list -> abes -> abes **)

let addrofbe_from_cmds nbs2 md =
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  addrofbe_from_smem st2.SBSE.coq_SMem md

(** val addrofbe_from_subblock : SBsyntax.subblock -> abes -> abes **)

let addrofbe_from_subblock sb2 md =
  let { SBsyntax.coq_NBs = nbs2; SBsyntax.call_cmd = call_cmd0 } = sb2 in
  addrofbe_from_cmds nbs2 md

(** val addrofbe_from_subblocks : SBsyntax.subblock list -> abes -> abes **)

let rec addrofbe_from_subblocks sbs2 md =
  match sbs2 with
    | [] -> md
    | sb2::sbs2' ->
        addrofbe_from_subblocks sbs2' (addrofbe_from_subblock sb2 md)

(** val addrofbe_from_block : SBsyntax.block -> abes -> abes **)

let addrofbe_from_block b2 md =
  match b2 with
    | SBsyntax.Coq_block_common (l2, ps2, sbs2, nbs2, t) ->
        let accum1 = addrofbe_from_cmds nbs2 md in
        addrofbe_from_subblocks sbs2 accum1
    | SBsyntax.Coq_block_ret_ptr (l2, ps2, sbs2, nbs2, i) ->
        let accum1 = addrofbe_from_cmds nbs2 md in
        addrofbe_from_subblocks sbs2 accum1

(** val addrofbe_from_blocks : SBsyntax.blocks -> abes -> abes **)

let rec addrofbe_from_blocks bs2 md =
  match bs2 with
    | [] -> md
    | b2::bs2' -> addrofbe_from_blocks bs2' (addrofbe_from_block b2 md)

(** val addrofbe_from_fdef : SBsyntax.fdef -> abes -> abes **)

let addrofbe_from_fdef f2 md =
  let SBsyntax.Coq_fdef_intro (fh2, lb2) = f2 in
  let LLVMsyntax.Coq_fheader_intro (f, t2, fid2, a2, v) = fh2 in
  if SBSE.isCallLib fid2 then md else addrofbe_from_blocks lb2 []

type fabes = (LLVMsyntax.id*abes) list

(** val addrofbe_from_products : SBsyntax.products -> fabes -> fabes **)

let rec addrofbe_from_products ps2 md =
  match ps2 with
    | [] -> md
    | p::ps2' ->
        (match p with
           | SBsyntax.Coq_product_fdef f2 ->
               let abes0 = addrofbe_from_fdef f2 [] in
               let md' = updateAddAL md (SBsyntax.getFdefID f2) abes0 in
               addrofbe_from_products ps2' md'
           | _ -> addrofbe_from_products ps2' md)

(** val addrofbe_from_module : SBsyntax.coq_module -> fabes **)

let addrofbe_from_module = function
  | SBsyntax.Coq_module_intro (l0, n, ps2) -> addrofbe_from_products ps2 []

