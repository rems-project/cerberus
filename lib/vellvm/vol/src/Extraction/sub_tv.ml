open BinInt
open BinPos
open Bool
open Datatypes
open EqNat
open List0
open Peano
open Zpower
open Alist
open Infrastructure
open Monad
open Sub_symexe
open Sub_tv_dec
open Sub_tv_def
open Sub_tv_infer
open Syntax

(** val smem_lib_sub : LLVMsyntax.id -> bool **)

let smem_lib_sub = Symexe_aux.smem_lib_sub

(** val load_from_metadata : SBSE.smem -> SBSE.sterm -> bool **)

let rec load_from_metadata sm ptr =
  match sm with
    | SBSE.Coq_smem_init -> false
    | SBSE.Coq_smem_malloc (sm1, t, s, a) -> load_from_metadata sm1 ptr
    | SBSE.Coq_smem_free (sm1, t, s) -> load_from_metadata sm1 ptr
    | SBSE.Coq_smem_alloca (sm1, t, s, a) -> load_from_metadata sm1 ptr
    | SBSE.Coq_smem_load (sm1, t, s, a) -> load_from_metadata sm1 ptr
    | SBSE.Coq_smem_store (sm1, t, s, s0, a) -> load_from_metadata sm1 ptr
    | SBSE.Coq_smem_lib (sm1, fid1, sts1) ->
        if is_hashLoadBaseBound fid1
        then (match sts1 with
                | SBSE.Nil_list_sterm -> load_from_metadata sm1 ptr
                | SBSE.Cons_list_sterm (s, l0) ->
                    (match l0 with
                       | SBSE.Nil_list_sterm -> load_from_metadata sm1 ptr
                       | SBSE.Cons_list_sterm (addr_of_base, l1) ->
                           (match l1 with
                              | SBSE.Nil_list_sterm ->
                                  load_from_metadata sm1 ptr
                              | SBSE.Cons_list_sterm (
                                  addr_of_bound, l2) ->
                                  (match l2 with
                                     | SBSE.Nil_list_sterm ->
                                         load_from_metadata sm1 ptr
                                     | SBSE.Cons_list_sterm (
                                         s0, l3) ->
                                         (match l3 with
                                            | SBSE.Nil_list_sterm ->
                                                load_from_metadata sm1 ptr
                                            | SBSE.Cons_list_sterm
                                                (s1, l4) ->
                                                (match l4 with
                                                   | 
                                                 SBSE.Nil_list_sterm ->
                                                  load_from_metadata sm1 ptr
                                                   | 
                                                 SBSE.Cons_list_sterm
                                                  (ptr_safe, l5) ->
                                                  (match l5 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  if 
                                                  if 
                                                  if 
                                                  eq_sterm_upto_cast ptr
                                                  addr_of_base
                                                  then true
                                                  else 
                                                  eq_sterm_upto_cast ptr
                                                  addr_of_bound
                                                  then true
                                                  else 
                                                  eq_sterm_upto_cast ptr
                                                  ptr_safe
                                                  then true
                                                  else 
                                                  load_from_metadata sm1 ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s2, l6) ->
                                                  load_from_metadata sm1 ptr)))))))
        else load_from_metadata sm1 ptr

(** val rename_id : LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id **)

let rename_id = Symexe_aux.rename_id

(** val tv_id : LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let tv_id fid id1 id2 =
  eq_id (rename_id fid id1) id2

(** val rename_fid : LLVMsyntax.id -> LLVMsyntax.id **)

let rename_fid = Symexe_aux.rename_fid

(** val tv_fid : LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let tv_fid fid1 fid2 =
  eq_id (rename_fid fid1) fid2

(** val tv_const :
    LLVMsyntax.id -> LLVMsyntax.const -> LLVMsyntax.const -> bool **)

let rec tv_const fid c c' =
  match c with
    | LLVMsyntax.Coq_const_zeroinitializer t0 ->
        (match c' with
           | LLVMsyntax.Coq_const_zeroinitializer t0' -> tv_typ t0 t0'
           | _ -> false)
    | LLVMsyntax.Coq_const_int (s, i) ->
        (match c' with
           | LLVMsyntax.Coq_const_int (s0, i0) -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_floatpoint (f, f0) ->
        (match c' with
           | LLVMsyntax.Coq_const_floatpoint (f1, f2) -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_undef t ->
        (match c' with
           | LLVMsyntax.Coq_const_undef t0 -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_null t ->
        (match c' with
           | LLVMsyntax.Coq_const_null t0 -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_arr (t0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_arr (t0', cs0') ->
               if tv_typ t0 t0' then tv_list_const fid cs0 cs0' else false
           | _ -> false)
    | LLVMsyntax.Coq_const_struct cs0 ->
        (match c' with
           | LLVMsyntax.Coq_const_struct cs0' -> tv_list_const fid cs0 cs0'
           | _ -> false)
    | LLVMsyntax.Coq_const_gid (t, id0) ->
        (match c' with
           | LLVMsyntax.Coq_const_gid (t0, id0') ->
               if tv_fid id0 id0' then true else tv_id fid id0 id0'
           | _ -> false)
    | LLVMsyntax.Coq_const_truncop (to0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_truncop (to0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.truncop_dec to0 to0')
                  then tv_const fid c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_extop (eo0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_extop (eo0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.extop_dec eo0 eo0')
                  then tv_const fid c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_castop (co0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_castop (co0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.castop_dec co0 co0')
                  then tv_const fid c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_gep (ib0, c0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_gep (ib0', c0', cs0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.inbounds_dec ib0 ib0')
                  then tv_const fid c0 c0'
                  else false
               then tv_list_const fid cs0 cs0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_select (c0, c1, c2) ->
        (match c' with
           | LLVMsyntax.Coq_const_select (c0', c1', c2') ->
               if if tv_const fid c0 c0' then tv_const fid c1 c1' else false
               then tv_const fid c2 c2'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_icmp (cd0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_icmp (cd0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.cond_dec cd0 cd0')
                  then tv_const fid c0 c0'
                  else false
               then tv_const fid c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_fcmp (fd0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_fcmp (fd0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fcond_dec fd0 fd0')
                  then tv_const fid c0 c0'
                  else false
               then tv_const fid c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_extractvalue (c0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_extractvalue (c0', cs0') ->
               if tv_const fid c0 c0'
               then tv_list_const fid cs0 cs0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_insertvalue (c0, c1, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_insertvalue (c0', c1', cs0') ->
               if if tv_const fid c0 c0' then tv_const fid c c1' else false
               then tv_list_const fid cs0 cs0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_bop (b0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_bop (b0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.bop_dec b0 b0')
                  then tv_const fid c0 c0'
                  else false
               then tv_const fid c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_fbop (f0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_fbop (f0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fbop_dec f0 f0')
                  then tv_const fid c0 c0'
                  else false
               then tv_const fid c1 c1'
               else false
           | _ -> false)

(** val tv_list_const :
    LLVMsyntax.id -> LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)

and tv_list_const fid cs cs' =
  match cs with
    | LLVMsyntax.Nil_list_const ->
        (match cs' with
           | LLVMsyntax.Nil_list_const -> true
           | LLVMsyntax.Cons_list_const (c, l0) -> false)
    | LLVMsyntax.Cons_list_const (c0, cs0) ->
        (match cs' with
           | LLVMsyntax.Nil_list_const -> false
           | LLVMsyntax.Cons_list_const (c0', cs0') ->
               if tv_const fid c0 c0'
               then tv_list_const fid cs0 cs0'
               else false)

(** val tv_value :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.value -> bool **)

let tv_value fid v1 v2 =
  match v1 with
    | LLVMsyntax.Coq_value_id id1 ->
        (match v2 with
           | LLVMsyntax.Coq_value_id id2 -> tv_id fid id1 id2
           | LLVMsyntax.Coq_value_const c -> false)
    | LLVMsyntax.Coq_value_const c1 ->
        (match v2 with
           | LLVMsyntax.Coq_value_id i -> false
           | LLVMsyntax.Coq_value_const c2 -> tv_const fid c1 c2)

(** val syscall_returns_pointer : LLVMsyntax.id -> bool **)

let syscall_returns_pointer = Symexe_aux.syscall_returns_pointer

(** val rename_fid_inv : LLVMsyntax.id -> LLVMsyntax.id option **)

let rename_fid_inv = Symexe_aux.rename_fid_inv

(** val function_returns_pointer :
    LLVMsyntax.products -> LLVMsyntax.id -> bool **)

let function_returns_pointer ps1 fid2 =
  match rename_fid_inv fid2 with
    | Some fid1 ->
        (match LLVMinfra.lookupFdefViaIDFromProducts ps1 fid1 with
           | Some f ->
               let LLVMsyntax.Coq_fdef_intro (f0, b) = f in
               let LLVMsyntax.Coq_fheader_intro (f1, tp, i, a, v) = f0 in
               (match tp with
                  | LLVMsyntax.Coq_typ_pointer t -> true
                  | _ -> false)
           | None -> false)
    | None -> false

(** val store_to_ret :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sterm
    -> bool **)

let store_to_ret ps1 ps2 fid2 ptr =
  if function_returns_pointer ps1 fid2
  then (match SBsyntax.lookupFdefViaIDFromProducts ps2 fid2 with
          | Some f ->
              let SBsyntax.Coq_fdef_intro (f0, b) = f in
              let LLVMsyntax.Coq_fheader_intro (f1, t, i, a, v) = f0 in
              (match a with
                 | [] -> false
                 | p::l0 ->
                     let p0,re = p in
                     (match remove_cast ptr with
                        | SBSE.Coq_sterm_gep (i0, t0, s, l1) ->
                            (match s with
                               | SBSE.Coq_sterm_val v0 ->
                                   (match v0 with
                                      | LLVMsyntax.Coq_value_id id0 ->
                                          (match l1 with
                                             | SBSE.Nil_list_sz_sterm ->
                                                 false
                                             | SBSE.Cons_list_sz_sterm
                                                 (s0, s1, l2) ->
                                                 (match s1 with
                                                    | 
                                                  SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c ->
                                                  (match c with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s2, i1) ->
                                                  (match l2 with
                                                    | 
                                                  SBSE.Nil_list_sz_sterm ->
                                                  false
                                                    | 
                                                  SBSE.Cons_list_sz_sterm
                                                  (s3, s4, l3) ->
                                                  (match s4 with
                                                    | 
                                                  SBSE.Coq_sterm_val v2 ->
                                                  (match v2 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i2 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c0 ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s5, i2) ->
                                                  (match l3 with
                                                    | 
                                                  SBSE.Nil_list_sz_sterm ->
                                                  if 
                                                  if eq_id id0 re
                                                  then eq_INT_Z i1 Z0
                                                  else false
                                                  then 
                                                  if 
                                                  if eq_INT_Z i2 Z0
                                                  then true
                                                  else 
                                                  eq_INT_Z i2 (Zpos Coq_xH)
                                                  then true
                                                  else 
                                                  eq_INT_Z i2 (Zpos (Coq_xO
                                                  Coq_xH))
                                                  else false
                                                    | 
                                                  SBSE.Cons_list_sz_sterm
                                                  (s6, s7, l4) -> false)
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  _ -> false))
                                      | LLVMsyntax.Coq_value_const c -> false)
                               | _ -> false)
                        | _ -> false))
          | None -> false)
  else false

(** val tv_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sterm
    -> SBSE.sterm -> bool **)

let rec tv_sterm ps1 ps2 fid st st' =
  match st with
    | SBSE.Coq_sterm_val v ->
        (match st' with
           | SBSE.Coq_sterm_val v' -> tv_value fid v v'
           | _ -> false)
    | SBSE.Coq_sterm_bop (b, sz, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_bop (b', sz', st1', st2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.bop_dec b b')
                     then LLVMinfra.sumbool2bool (LLVMsyntax.Size.dec sz sz')
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_sterm ps1 ps2 fid st2 st2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_fbop (b, f, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_fbop (b', f', st1', st2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.fbop_dec b b')
                     then LLVMinfra.sumbool2bool
                            (LLVMinfra.floating_point_dec f f')
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_sterm ps1 ps2 fid st2 st2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_extractvalue (t, st1, cs) ->
        (match st' with
           | SBSE.Coq_sterm_extractvalue (t', st1', cs') ->
               if if tv_typ t t'
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then LLVMinfra.sumbool2bool (LLVMinfra.list_const_dec cs cs')
               else false
           | _ -> false)
    | SBSE.Coq_sterm_insertvalue (t1, st1, t2, st2, cs) ->
        (match st' with
           | SBSE.Coq_sterm_insertvalue (t1', st1', t2', st2', cs') ->
               if if if if tv_typ t1 t1'
                        then tv_sterm ps1 ps2 fid st1 st1'
                        else false
                     then tv_typ t2 t2'
                     else false
                  then tv_sterm ps1 ps2 fid st2 st2'
                  else false
               then LLVMinfra.sumbool2bool (LLVMinfra.list_const_dec cs cs')
               else false
           | _ -> false)
    | SBSE.Coq_sterm_malloc (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_malloc (sm', t', st1', a') ->
               if if if tv_smem ps1 ps2 fid sm sm'
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_align a a'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_alloca (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_alloca (sm', t', st1', a') ->
               if if if tv_smem ps1 ps2 fid sm sm'
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_align a a'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_load (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_load (sm', t', st1', a') ->
               if if if tv_smem ps1 ps2 fid sm sm'
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_align a a'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_gep (i, t, st1, sts2) ->
        (match st' with
           | SBSE.Coq_sterm_gep (i', t', st1', sts2') ->
               if if if LLVMinfra.sumbool2bool (bool_dec i i')
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_list_sz_sterm ps1 ps2 fid sts2 sts2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_trunc (top, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_trunc (top', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool
                          (LLVMinfra.truncop_dec top top')
                     then tv_typ t1 t1'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_typ t2 t2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_ext (eo, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_ext (eo', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.extop_dec eo eo')
                     then tv_typ t1 t1'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_typ t2 t2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_cast (co, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_cast (co', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.castop_dec co co')
                     then tv_typ t1 t1'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_typ t2 t2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_icmp (c, t, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_icmp (c', t', st1', st2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.cond_dec c c')
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_sterm ps1 ps2 fid st2 st2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_fcmp (c, ft, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_fcmp (c', ft', st1', st2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.fcond_dec c c')
                     then LLVMinfra.sumbool2bool
                            (LLVMinfra.floating_point_dec ft ft')
                     else false
                  then tv_sterm ps1 ps2 fid st1 st1'
                  else false
               then tv_sterm ps1 ps2 fid st2 st2'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_phi (t, stls) ->
        (match st' with
           | SBSE.Coq_sterm_phi (t', stls') ->
               if tv_typ t t'
               then tv_list_sterm_l ps1 ps2 fid stls stls'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_select (st1, t, st2, st3) ->
        (match st' with
           | SBSE.Coq_sterm_select (st1', t', st2', st3') ->
               if if if tv_sterm ps1 ps2 fid st1 st1'
                     then tv_typ t t'
                     else false
                  then tv_sterm ps1 ps2 fid st2 st2'
                  else false
               then tv_sterm ps1 ps2 fid st3 st3'
               else false
           | _ -> false)
    | SBSE.Coq_sterm_lib (sm, i, sts) ->
        (match st' with
           | SBSE.Coq_sterm_lib (sm', i', sts') ->
               if if tv_smem ps1 ps2 fid sm sm' then eq_id i i' else false
               then tv_list_sterm ps1 ps2 fid sts sts'
               else false
           | _ -> false)

(** val tv_list_sz_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBSE.list_sz_sterm -> SBSE.list_sz_sterm -> bool **)

and tv_list_sz_sterm ps1 ps2 fid sts sts' =
  match sts with
    | SBSE.Nil_list_sz_sterm ->
        (match sts' with
           | SBSE.Nil_list_sz_sterm -> true
           | SBSE.Cons_list_sz_sterm (s, s0, l0) -> false)
    | SBSE.Cons_list_sz_sterm (sz0, st, sts0) ->
        (match sts' with
           | SBSE.Nil_list_sz_sterm -> false
           | SBSE.Cons_list_sz_sterm (sz0', st', sts0') ->
               if if LLVMinfra.sumbool2bool (LLVMsyntax.Size.dec sz0 sz0')
                  then tv_sterm ps1 ps2 fid st st'
                  else false
               then tv_list_sz_sterm ps1 ps2 fid sts0 sts0'
               else false)

(** val tv_list_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBSE.list_sterm -> SBSE.list_sterm -> bool **)

and tv_list_sterm ps1 ps2 fid sts sts' =
  match sts with
    | SBSE.Nil_list_sterm ->
        (match sts' with
           | SBSE.Nil_list_sterm -> true
           | SBSE.Cons_list_sterm (s, l0) -> false)
    | SBSE.Cons_list_sterm (st, sts0) ->
        (match sts' with
           | SBSE.Nil_list_sterm -> false
           | SBSE.Cons_list_sterm (st', sts0') ->
               if tv_sterm ps1 ps2 fid st st'
               then tv_list_sterm ps1 ps2 fid sts0 sts0'
               else false)

(** val tv_list_sterm_l :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBSE.list_sterm_l -> SBSE.list_sterm_l -> bool **)

and tv_list_sterm_l ps1 ps2 fid stls stls' =
  match stls with
    | SBSE.Nil_list_sterm_l ->
        (match stls' with
           | SBSE.Nil_list_sterm_l -> true
           | SBSE.Cons_list_sterm_l (s, l0, l1) -> false)
    | SBSE.Cons_list_sterm_l (st, l0, stls0) ->
        (match stls' with
           | SBSE.Nil_list_sterm_l -> false
           | SBSE.Cons_list_sterm_l (st', l', stls0') ->
               if if tv_sterm ps1 ps2 fid st st'
                  then LLVMinfra.sumbool2bool (LLVMinfra.l_dec l0 l')
                  else false
               then tv_list_sterm_l ps1 ps2 fid stls0 stls0'
               else false)

(** val tv_smem :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.smem ->
    SBSE.smem -> bool **)

and tv_smem ps1 ps2 fid sm1 sm2 =
  match sm1 with
    | SBSE.Coq_smem_init -> true
    | SBSE.Coq_smem_malloc (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_malloc (sm4, t2, st2, a2) ->
               if if if tv_smem ps1 ps2 fid sm3 sm4
                     then tv_typ t1 t2
                     else false
                  then tv_sterm ps1 ps2 fid st1 st2
                  else false
               then tv_align a1 a2
               else false
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               tv_smem ps1 ps2 fid sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then load_from_metadata sm4 st2
               else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then store_to_ret ps1 ps2 (rename_fid fid) st22
               else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then tv_smem ps1 ps2 fid sm1 sm4
               else false
           | _ -> false)
    | SBSE.Coq_smem_free (sm3, t1, st1) ->
        (match sm2 with
           | SBSE.Coq_smem_free (sm4, t2, st2) ->
               if if tv_smem ps1 ps2 fid sm3 sm4 then tv_typ t1 t2 else false
               then tv_sterm ps1 ps2 fid st1 st2
               else false
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               tv_smem ps1 ps2 fid sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then load_from_metadata sm4 st2
               else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then store_to_ret ps1 ps2 (rename_fid fid) st22
               else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then tv_smem ps1 ps2 fid sm1 sm4
               else false
           | _ -> false)
    | SBSE.Coq_smem_alloca (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               if if if tv_typ t1 t2
                     then tv_sterm ps1 ps2 fid st1 st2
                     else false
                  then tv_align a1 a2
                  else false
               then tv_smem ps1 ps2 fid sm3 sm4
               else tv_smem ps1 ps2 fid (SBSE.Coq_smem_alloca (sm3, t1, st1,
                      a1)) sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then load_from_metadata sm4 st2
               else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then store_to_ret ps1 ps2 (rename_fid fid) st22
               else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then tv_smem ps1 ps2 fid sm1 sm4
               else false
           | _ -> false)
    | SBSE.Coq_smem_load (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               tv_smem ps1 ps2 fid sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if if if tv_typ t1 t2
                     then tv_sterm ps1 ps2 fid st1 st2
                     else false
                  then tv_align a1 a2
                  else false
               then tv_smem ps1 ps2 fid sm3 sm4
               else if tv_smem ps1 ps2 fid (SBSE.Coq_smem_load (sm3, t1, st1,
                         a1)) sm4
                    then load_from_metadata sm4 st2
                    else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then store_to_ret ps1 ps2 (rename_fid fid) st22
               else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then tv_smem ps1 ps2 fid sm1 sm4
               else false
           | _ -> false)
    | SBSE.Coq_smem_store (sm3, t1, st11, st12, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               tv_smem ps1 ps2 fid sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then load_from_metadata sm4 st2
               else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if if if if tv_typ t1 t2
                        then tv_sterm ps1 ps2 fid st11 st21
                        else false
                     then tv_sterm ps1 ps2 fid st12 st22
                     else false
                  then tv_align a1 a2
                  else false
               then tv_smem ps1 ps2 fid sm3 sm4
               else if tv_smem ps1 ps2 fid (SBSE.Coq_smem_store (sm3, t1,
                         st11, st12, a1)) sm4
                    then store_to_ret ps1 ps2 (rename_fid fid) st22
                    else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then tv_smem ps1 ps2 fid sm1 sm4
               else false
           | _ -> false)
    | SBSE.Coq_smem_lib (sm3, fid1, sts1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               tv_smem ps1 ps2 fid sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then load_from_metadata sm4 st2
               else false
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if tv_smem ps1 ps2 fid sm1 sm4
               then store_to_ret ps1 ps2 (rename_fid fid) st22
               else false
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if if eq_id fid1 lid
                  then tv_list_sterm ps1 ps2 fid sts1 sts
                  else false
               then tv_smem ps1 ps2 fid sm3 sm4
               else tv_smem ps1 ps2 fid (SBSE.Coq_smem_lib (sm3, fid1, sts1))
                      sm4
           | _ -> false)

(** val tv_sframe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sframe
    -> SBSE.sframe -> bool **)

let rec tv_sframe ps1 ps2 fid sf1 sf2 =
  match sf1 with
    | SBSE.Coq_sframe_init -> true
    | SBSE.Coq_sframe_alloca (sm1, sf3, t1, st1, a1) ->
        (match sf2 with
           | SBSE.Coq_sframe_init -> false
           | SBSE.Coq_sframe_alloca (sm2, sf4, t2, st2, a2) ->
               if if if if tv_smem ps1 ps2 fid sm1 sm2
                        then tv_typ t1 t2
                        else false
                     then tv_sterm ps1 ps2 fid st1 st2
                     else false
                  then tv_align a1 a2
                  else false
               then tv_sframe ps1 ps2 fid sf3 sf4
               else tv_sframe ps1 ps2 fid (SBSE.Coq_sframe_alloca (sm1, sf3,
                      t1, st1, a1)) sf4)

(** val tv_smap :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.smap ->
    SBSE.smap -> bool **)

let rec tv_smap ps1 ps2 fid sm1 sm2 =
  match sm1 with
    | [] -> true
    | p::sm1' ->
        let id1,st1 = p in
        (match lookupAL sm2 (rename_id fid id1) with
           | Some st2 ->
               if tv_sterm ps1 ps2 fid st1 st2
               then tv_smap ps1 ps2 fid sm1' sm2
               else false
           | None -> false)

(** val sub_sstate :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.sstate
    -> SBSE.sstate -> bool **)

let sub_sstate ps1 ps2 fid s1 s2 =
  if if if tv_smap ps1 ps2 fid s1.SBSE.coq_STerms s2.SBSE.coq_STerms
        then tv_smem ps1 ps2 fid s1.SBSE.coq_SMem s2.SBSE.coq_SMem
        else false
     then tv_sframe ps1 ps2 fid s1.SBSE.coq_SFrame s2.SBSE.coq_SFrame
     else false
  then LLVMinfra.sumbool2bool
         (SBSE.sterms_dec s1.SBSE.coq_SEffects s2.SBSE.coq_SEffects)
  else false

(** val tv_cmds :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> SBSE.nbranch
    list -> SBSE.nbranch list -> bool **)

let tv_cmds ps1 ps2 fid nbs1 nbs2 =
  sub_sstate ps1 ps2 fid (SBSE.se_cmds SBSE.sstate_init nbs1)
    (SBSE.se_cmds SBSE.sstate_init nbs2)

(** val tv_sparams :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> bool **)

let rec tv_sparams ps1 ps2 fid tsts1 tsts2 =
  match tsts1 with
    | [] -> true
    | p::tsts1' ->
        let p0,st1 = p in
        let t1,a = p0 in
        (match tsts2 with
           | [] -> false
           | p1::tsts2' ->
               let p2,st2 = p1 in
               let t2,a0 = p2 in
               if if tv_typ t1 t2
                  then tv_sterm ps1 ps2 fid st1 st2
                  else false
               then tv_sparams ps1 ps2 fid tsts1' tsts2'
               else false)

type scall =
  | Coq_stmn_call of LLVMsyntax.id * LLVMsyntax.noret * 
     LLVMsyntax.clattrs * LLVMsyntax.typ * SBSE.sterm
     * ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list

(** val scall_rect :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> 'a1) -> scall
    -> 'a1 **)

let scall_rect f = function
  | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4

(** val scall_rec :
    (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> SBSE.sterm ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> 'a1) -> scall
    -> 'a1 **)

let scall_rec f = function
  | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4

(** val se_call : SBSE.sstate -> LLVMsyntax.cmd -> scall **)

let se_call st = function
  | LLVMsyntax.Coq_insn_call (i1, n, c, t, v, p) -> Coq_stmn_call (i1, n, c,
      t, (SBSE.value2Sterm st.SBSE.coq_STerms v),
      (SBSE.list_param__list_typ_subst_sterm p st.SBSE.coq_STerms))
  | _ -> assert false (* absurd case *)

(** val tv_scall :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> scall ->
    sicall -> bool **)

let tv_scall ps1 ps2 fid c1 c2 =
  let Coq_stmn_call (rid1, nr1, c, ty1, t1, tsts1) = c1 in
  (match c2 with
     | Coq_stmn_icall_nptr (rid2, nr2, c0, ty2, t2, tsts2) ->
         if if if if tv_id fid rid1 rid2
                  then LLVMinfra.sumbool2bool (LLVMinfra.noret_dec nr1 nr2)
                  else false
               then tv_typ ty1 ty2
               else false
            then tv_sparams ps1 ps2 fid tsts1 tsts2
            else false
         then tv_sterm ps1 ps2 fid (remove_cast t1) (remove_cast t2)
         else false
     | Coq_stmn_icall_ptr
         (i, n, c0, ty2, t2, tsts2, i0, i1, rid2, i2, i3, i4, i5, c3, c4, c5) ->
         if if if tv_id fid rid1 rid2 then tv_typ ty1 ty2 else false
            then tv_sparams ps1 ps2 fid tsts1 tsts2
            else false
         then (match ty1 with
                 | LLVMsyntax.Coq_typ_pointer t ->
                     let st1 = remove_cast t1 in
                     let st2 = remove_cast t2 in
                     (match st1 with
                        | SBSE.Coq_sterm_val v ->
                            (match v with
                               | LLVMsyntax.Coq_value_id i6 ->
                                   tv_sterm ps1 ps2 fid st1 st2
                               | LLVMsyntax.Coq_value_const c6 ->
                                   (match c6 with
                                      | LLVMsyntax.Coq_const_gid
                                          (t0, fid1) ->
                                          (match st2 with
                                             | SBSE.Coq_sterm_val v0 ->
                                                 (match v0 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i6 ->
                                                  tv_sterm ps1 ps2 fid st1
                                                  st2
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c7 ->
                                                  (match c7 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t3, fid2) ->
                                                  tv_fid fid1 fid2
                                                    | 
                                                  _ ->
                                                  tv_sterm ps1 ps2 fid st1
                                                  st2))
                                             | _ ->
                                                 tv_sterm ps1 ps2 fid st1 st2)
                                      | _ -> tv_sterm ps1 ps2 fid st1 st2))
                        | _ -> tv_sterm ps1 ps2 fid st1 st2)
                 | _ -> false)
         else false)

(** val tv_subblock :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBSE.subblock -> SBsyntax.subblock -> bool **)

let tv_subblock ps1 ps2 fid sb1 sb2 =
  let { SBSE.coq_NBs = nbs1; SBSE.call_cmd = call1 } = sb1 in
  let { SBsyntax.coq_NBs = nbs2; SBsyntax.call_cmd = call2 } = sb2 in
  let st1 = SBSE.se_cmds SBSE.sstate_init nbs1 in
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  let cl1 = se_call st1 call1 in
  let cl2 = se_icall st2 call2 in
  if sub_sstate ps1 ps2 fid st1 st2
  then tv_scall ps1 ps2 fid cl1 cl2
  else false

(** val tv_subblocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBSE.subblock list -> SBsyntax.subblock list -> bool **)

let rec tv_subblocks ps1 ps2 fid sbs1 sbs2 =
  match sbs1 with
    | [] -> (match sbs2 with
               | [] -> true
               | s::l0 -> false)
    | sb1::sbs1' ->
        (match sbs2 with
           | [] -> false
           | sb2::sbs2' ->
               if tv_subblock ps1 ps2 fid sb1 sb2
               then tv_subblocks ps1 ps2 fid sbs1' sbs2'
               else false)

(** val tv_list_value_l :
    LLVMsyntax.id -> LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l ->
    bool **)

let rec tv_list_value_l fid vls1 vls2 =
  match vls1 with
    | LLVMsyntax.Nil_list_value_l ->
        (match vls2 with
           | LLVMsyntax.Nil_list_value_l -> true
           | LLVMsyntax.Cons_list_value_l (v, l0, l1) -> false)
    | LLVMsyntax.Cons_list_value_l (v1, l1, vls3) ->
        (match vls2 with
           | LLVMsyntax.Nil_list_value_l -> false
           | LLVMsyntax.Cons_list_value_l (v2, l2, vls4) ->
               if if tv_value fid v1 v2 then eq_l l1 l2 else false
               then tv_list_value_l fid vls3 vls4
               else false)

(** val tv_phinode :
    LLVMsyntax.id -> LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)

let tv_phinode fid p1 p2 =
  let LLVMsyntax.Coq_insn_phi (id1, t1, vls1) = p1 in
  let LLVMsyntax.Coq_insn_phi (id2, t2, vls2) = p2 in
  if if tv_id fid id1 id2 then tv_typ t1 t2 else false
  then tv_list_value_l fid vls1 vls2
  else false

(** val tv_phinodes :
    LLVMsyntax.id -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> bool **)

let rec tv_phinodes fid ps1 ps2 =
  match ps1 with
    | [] -> true
    | p1::ps1' ->
        let LLVMsyntax.Coq_insn_phi (i1, t, l0) = p1 in
        (match lookupPhinode ps2 (rename_id fid i1) with
           | Some p2 ->
               if tv_phinode fid p1 p2
               then tv_phinodes fid ps1' ps2
               else false
           | None -> false)

(** val tv_terminator :
    LLVMsyntax.id -> LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool **)

let tv_terminator fid tmn1 tmn2 =
  match tmn1 with
    | LLVMsyntax.Coq_insn_return (id1, t1, v1) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return (id2, t2, v2) ->
               if if tv_id fid id1 id2 then tv_typ t1 t2 else false
               then tv_value fid v1 v2
               else false
           | _ -> false)
    | LLVMsyntax.Coq_insn_return_void id1 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return_void id2 -> tv_id fid id1 id2
           | _ -> false)
    | LLVMsyntax.Coq_insn_br (id1, v1, l11, l12) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br (id2, v2, l21, l22) ->
               if if if tv_id fid id1 id2 then tv_value fid v1 v2 else false
                  then eq_l l11 l21
                  else false
               then eq_l l12 l22
               else false
           | _ -> false)
    | LLVMsyntax.Coq_insn_br_uncond (id1, l1) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br_uncond (id2, l2) ->
               if tv_id fid id1 id2 then eq_l l1 l2 else false
           | _ -> false)
    | LLVMsyntax.Coq_insn_unreachable id1 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_unreachable id2 -> tv_id fid id1 id2
           | _ -> false)

(** val tv_block :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.block -> SBsyntax.block -> bool **)

let tv_block ps1 ps2 fid b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps3, cs1, tmn1) = b1 in
  (match b2 with
     | SBsyntax.Coq_block_common (l2, ps4, sbs2, nbs2, tmn2) ->
         let sbs1,nbs1 = SBSE.cmds2sbs cs1 in
         if if if if eq_l l1 l2 then tv_phinodes fid ps3 ps4 else false
               then tv_subblocks ps1 ps2 fid sbs1 sbs2
               else false
            then tv_cmds ps1 ps2 fid nbs1 nbs2
            else false
         then tv_terminator fid tmn1 tmn2
         else false
     | SBsyntax.Coq_block_ret_ptr (l2, ps4, sbs2, nbs2, i) ->
         let SBsyntax.Coq_insn_return_ptr
           (i0, t, i1, i2, i3, v, i4, i5, v0, i6, vp, i7, c, c0, c1) = i
         in
         let sbs1,nbs1 = SBSE.cmds2sbs cs1 in
         if if if if eq_l l1 l2 then tv_phinodes fid ps3 ps4 else false
               then tv_subblocks ps1 ps2 fid sbs1 sbs2
               else false
            then tv_cmds ps1 ps2 fid nbs1 nbs2
            else false
         then (match tmn1 with
                 | LLVMsyntax.Coq_insn_return (id1, t0, v1) ->
                     tv_value fid v1 vp
                 | _ -> false)
         else false)

(** val tv_blocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.blocks -> SBsyntax.blocks -> bool **)

let rec tv_blocks ps1 ps2 fid bs1 bs2 =
  match bs1 with
    | [] -> (match bs2 with
               | [] -> true
               | b::l0 -> false)
    | b1::bs1' ->
        (match bs2 with
           | [] -> false
           | b2::bs2' ->
               if tv_block ps1 ps2 fid b1 b2
               then tv_blocks ps1 ps2 fid bs1' bs2'
               else false)

(** val tv_fheader :
    LLVMsyntax.namedt list -> LLVMsyntax.fheader -> LLVMsyntax.fheader ->
    bool **)

let tv_fheader nts1 f1 f2 =
  let LLVMsyntax.Coq_fheader_intro (fa1, t1, fid1, a1, va1) = f1 in
  let LLVMsyntax.Coq_fheader_intro (fa2, t2, fid2, a2, va2) = f2 in
  if tv_fid fid1 fid2
  then (match t1 with
          | LLVMsyntax.Coq_typ_pointer t ->
              (match a2 with
                 | [] -> false
                 | p::a2' ->
                     let p0,i = p in
                     let t0,a = p0 in
                     (match t0 with
                        | LLVMsyntax.Coq_typ_pointer t3 ->
                            (match SBsyntax.get_ret_typs nts1 t3 with
                               | Some p1 ->
                                   let p2,t03 = p1 in
                                   let t01,t02 = p2 in
                                   if if if tv_typ t1 t01
                                         then tv_typ t02 t03
                                         else false
                                      then tv_typ t02
                                             (LLVMsyntax.Coq_typ_pointer
                                             (LLVMsyntax.Coq_typ_int
                                             LLVMsyntax.Size.coq_Eight))
                                      else false
                                   then if syscall_returns_pointer fid1
                                        then let ts1 = LLVMinfra.args2Typs a1
                                             in
                                             let ts2' =
                                               LLVMinfra.args2Typs a2'
                                             in
                                             LLVMinfra.sumbool2bool
                                               (prefix_dec LLVMinfra.typ_dec
                                                 (LLVMsyntax.unmake_list_typ
                                                  ts1)
                                                 (LLVMsyntax.unmake_list_typ
                                                  ts2'))
                                        else LLVMinfra.sumbool2bool
                                               (prefix_dec LLVMinfra.arg_dec
                                                 a1 a2')
                                   else false
                               | None -> false)
                        | _ -> false))
          | _ ->
              if tv_typ t1 t2
              then LLVMinfra.sumbool2bool
                     (prefix_dec LLVMinfra.arg_dec a1 a2)
              else false)
  else false

(** val tv_fdec :
    LLVMsyntax.namedt list -> LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)

let tv_fdec nts1 f1 f2 =
  tv_fheader nts1 f1 f2

(** val tv_fdef :
    LLVMsyntax.namedt list -> LLVMsyntax.products -> SBsyntax.products ->
    LLVMsyntax.fdef -> SBsyntax.fdef -> bool **)

let tv_fdef nts1 ps1 ps2 f1 f2 =
  let LLVMsyntax.Coq_fdef_intro (fh1, lb1) = f1 in
  let LLVMsyntax.Coq_fheader_intro (f, t, fid1, a, v) = fh1 in
  let fh2 = LLVMsyntax.Coq_fheader_intro (f, t, fid1, a, v) in
  let SBsyntax.Coq_fdef_intro (fh3, lb2) = f2 in
  if tv_fheader nts1 fh2 fh3 then tv_blocks ps1 ps2 fid1 lb1 lb2 else false

(** val tv_products :
    LLVMsyntax.namedt list -> LLVMsyntax.products -> LLVMsyntax.products ->
    SBsyntax.products -> bool **)

let rec tv_products nts1 ps10 ps1 ps2 =
  match ps1 with
    | [] -> true
    | p::ps1' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gv1 ->
               (match SBsyntax.lookupGvarViaIDFromProducts ps2
                        (LLVMinfra.getGvarID gv1) with
                  | Some gv2 ->
                      if LLVMinfra.sumbool2bool (LLVMinfra.gvar_dec gv1 gv2)
                      then tv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false)
           | LLVMsyntax.Coq_product_fdec f1 ->
               (match SBsyntax.lookupFdecViaIDFromProducts ps2
                        (rename_fid (LLVMinfra.getFdecID f1)) with
                  | Some f2 ->
                      if tv_fdec nts1 f1 f2
                      then tv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false)
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match SBsyntax.lookupFdefViaIDFromProducts ps2
                        (rename_fid (LLVMinfra.getFdefID f1)) with
                  | Some f2 ->
                      if tv_fdef nts1 ps10 ps2 f1 f2
                      then tv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false))

(** val tv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool **)

let tv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (los1, nts1, ps1) = m1 in
  let SBsyntax.Coq_module_intro (los2, nts2, ps2) = m2 in
  if if LLVMinfra.sumbool2bool (LLVMinfra.layouts_dec los1 los2)
     then LLVMinfra.sumbool2bool (LLVMinfra.namedts_dec nts1 nts2)
     else false
  then tv_products nts1 ps1 ps1 ps2
  else false

(** val tv_system : LLVMsyntax.system -> SBsyntax.system -> bool **)

let rec tv_system s1 s2 =
  match s1 with
    | [] -> (match s2 with
               | [] -> true
               | m::l0 -> false)
    | m1::s1' ->
        (match s2 with
           | [] -> false
           | m2::s2' -> if tv_module m1 m2 then tv_system s1' s2' else false)

(** val rtv_const : LLVMsyntax.const -> LLVMsyntax.const -> bool **)

let rec rtv_const c c' =
  match c with
    | LLVMsyntax.Coq_const_zeroinitializer t0 ->
        (match c' with
           | LLVMsyntax.Coq_const_zeroinitializer t0' -> tv_typ t0 t0'
           | _ -> false)
    | LLVMsyntax.Coq_const_int (s, i) ->
        (match c' with
           | LLVMsyntax.Coq_const_int (s0, i0) -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_floatpoint (f, f0) ->
        (match c' with
           | LLVMsyntax.Coq_const_floatpoint (f1, f2) -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_undef t ->
        (match c' with
           | LLVMsyntax.Coq_const_undef t0 -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_null t ->
        (match c' with
           | LLVMsyntax.Coq_const_null t0 -> eq_const c c'
           | _ -> false)
    | LLVMsyntax.Coq_const_arr (t0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_arr (t0', cs0') ->
               if tv_typ t0 t0' then rtv_list_const cs0 cs0' else false
           | _ -> false)
    | LLVMsyntax.Coq_const_struct cs0 ->
        (match c' with
           | LLVMsyntax.Coq_const_struct cs0' -> rtv_list_const cs0 cs0'
           | _ -> false)
    | LLVMsyntax.Coq_const_gid (t, id0) ->
        (match c' with
           | LLVMsyntax.Coq_const_gid (t0, id0') ->
               if tv_fid id0 id0' then true else eq_id id0 id0'
           | _ -> false)
    | LLVMsyntax.Coq_const_truncop (to0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_truncop (to0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.truncop_dec to0 to0')
                  then rtv_const c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_extop (eo0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_extop (eo0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.extop_dec eo0 eo0')
                  then rtv_const c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_castop (co0, c0, t0) ->
        (match c' with
           | LLVMsyntax.Coq_const_castop (co0', c0', t0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.castop_dec co0 co0')
                  then rtv_const c0 c0'
                  else false
               then tv_typ t0 t0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_gep (ib0, c0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_gep (ib0', c0', cs0') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.inbounds_dec ib0 ib0')
                  then rtv_const c0 c0'
                  else false
               then rtv_list_const cs0 cs0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_select (c0, c1, c2) ->
        (match c' with
           | LLVMsyntax.Coq_const_select (c0', c1', c2') ->
               if if rtv_const c0 c0' then rtv_const c1 c1' else false
               then rtv_const c2 c2'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_icmp (cd0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_icmp (cd0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.cond_dec cd0 cd0')
                  then rtv_const c0 c0'
                  else false
               then rtv_const c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_fcmp (fd0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_fcmp (fd0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fcond_dec fd0 fd0')
                  then rtv_const c0 c0'
                  else false
               then rtv_const c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_extractvalue (c0, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_extractvalue (c0', cs0') ->
               if rtv_const c0 c0' then rtv_list_const cs0 cs0' else false
           | _ -> false)
    | LLVMsyntax.Coq_const_insertvalue (c0, c1, cs0) ->
        (match c' with
           | LLVMsyntax.Coq_const_insertvalue (c0', c1', cs0') ->
               if if rtv_const c0 c0' then rtv_const c c1' else false
               then rtv_list_const cs0 cs0'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_bop (b0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_bop (b0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.bop_dec b0 b0')
                  then rtv_const c0 c0'
                  else false
               then rtv_const c1 c1'
               else false
           | _ -> false)
    | LLVMsyntax.Coq_const_fbop (f0, c0, c1) ->
        (match c' with
           | LLVMsyntax.Coq_const_fbop (f0', c0', c1') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fbop_dec f0 f0')
                  then rtv_const c0 c0'
                  else false
               then rtv_const c1 c1'
               else false
           | _ -> false)

(** val rtv_list_const :
    LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)

and rtv_list_const cs cs' =
  match cs with
    | LLVMsyntax.Nil_list_const ->
        (match cs' with
           | LLVMsyntax.Nil_list_const -> true
           | LLVMsyntax.Cons_list_const (c, l0) -> false)
    | LLVMsyntax.Cons_list_const (c0, cs0) ->
        (match cs' with
           | LLVMsyntax.Nil_list_const -> false
           | LLVMsyntax.Cons_list_const (c0', cs0') ->
               if rtv_const c0 c0' then rtv_list_const cs0 cs0' else false)

type renaming = (LLVMsyntax.id*LLVMsyntax.id) list

(** val is_tmp_var : LLVMsyntax.id -> bool **)

let is_tmp_var = Symexe_aux.is_tmp_var

(** val lookup_renaming :
    LLVMsyntax.id coq_AssocList -> LLVMsyntax.id -> LLVMsyntax.id option **)

let lookup_renaming r i =
  if is_tmp_var i then lookupAL r i else Some i

(** val rtv_id : renaming -> LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let rtv_id r id1 id2 =
  match lookup_renaming r id1 with
    | Some id2' -> eq_id id2 id2'
    | None -> eq_id id1 id2

(** val rtv_value :
    LLVMsyntax.id coq_AssocList -> LLVMsyntax.value -> LLVMsyntax.value ->
    renaming option **)

let rtv_value r v1 v2 =
  match v1 with
    | LLVMsyntax.Coq_value_id id1 ->
        (match v2 with
           | LLVMsyntax.Coq_value_id id2 ->
               (match lookup_renaming r id1 with
                  | Some id2' -> if eq_id id2 id2' then Some r else None
                  | None -> Some ((id1,id2)::r))
           | LLVMsyntax.Coq_value_const c -> None)
    | LLVMsyntax.Coq_value_const c1 ->
        (match v2 with
           | LLVMsyntax.Coq_value_id i -> None
           | LLVMsyntax.Coq_value_const c2 ->
               if rtv_const c1 c2 then Some r else None)

(** val rtv_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.id coq_AssocList -> SBSE.sterm -> SBSE.sterm -> renaming
    option **)

let rec rtv_sterm ps1 ps2 fid r st st' =
  match st with
    | SBSE.Coq_sterm_val v ->
        (match st' with
           | SBSE.Coq_sterm_val v' -> rtv_value r v v'
           | _ -> None)
    | SBSE.Coq_sterm_bop (b, sz, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_bop (b', sz', st1', st2') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.bop_dec b b')
                  then LLVMinfra.sumbool2bool (LLVMsyntax.Size.dec sz sz')
                  else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_fbop (b, f, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_fbop (b', f', st1', st2') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fbop_dec b b')
                  then LLVMinfra.sumbool2bool
                         (LLVMinfra.floating_point_dec f f')
                  else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_extractvalue (t, st1, cs) ->
        (match st' with
           | SBSE.Coq_sterm_extractvalue (t', st1', cs') ->
               if if tv_typ t t'
                  then LLVMinfra.sumbool2bool
                         (LLVMinfra.list_const_dec cs cs')
                  else false
               then rtv_sterm ps1 ps2 fid r st1 st1'
               else None
           | _ -> None)
    | SBSE.Coq_sterm_insertvalue (t1, st1, t2, st2, cs) ->
        (match st' with
           | SBSE.Coq_sterm_insertvalue (t1', st1', t2', st2', cs') ->
               if if if tv_typ t1 t1' then tv_typ t2 t2' else false
                  then LLVMinfra.sumbool2bool
                         (LLVMinfra.list_const_dec cs cs')
                  else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_malloc (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_malloc (sm', t', st1', a') ->
               if if tv_typ t t' then tv_align a a' else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st1 st1')
                      (rtv_smem ps1 ps2 fid r sm sm')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_alloca (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_alloca (sm', t', st1', a') ->
               if if tv_typ t t' then tv_align a a' else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st1 st1')
                      (rtv_smem ps1 ps2 fid r sm sm')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_load (sm, t, st1, a) ->
        (match st' with
           | SBSE.Coq_sterm_load (sm', t', st1', a') ->
               if if tv_typ t t' then tv_align a a' else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st1 st1')
                      (rtv_smem ps1 ps2 fid r sm sm')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_gep (i, t, st1, sts2) ->
        (match st' with
           | SBSE.Coq_sterm_gep (i', t', st1', sts2') ->
               if if LLVMinfra.sumbool2bool (bool_dec i i')
                  then tv_typ t t'
                  else false
               then mbind (fun r0 ->
                      rtv_list_sz_sterm ps1 ps2 fid r0 sts2 sts2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_trunc (top, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_trunc (top', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool
                          (LLVMinfra.truncop_dec top top')
                     then tv_typ t1 t1'
                     else false
                  then tv_typ t2 t2'
                  else false
               then rtv_sterm ps1 ps2 fid r st1 st1'
               else None
           | _ -> None)
    | SBSE.Coq_sterm_ext (eo, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_ext (eo', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.extop_dec eo eo')
                     then tv_typ t1 t1'
                     else false
                  then tv_typ t2 t2'
                  else false
               then rtv_sterm ps1 ps2 fid r st1 st1'
               else None
           | _ -> None)
    | SBSE.Coq_sterm_cast (co, t1, st1, t2) ->
        (match st' with
           | SBSE.Coq_sterm_cast (co', t1', st1', t2') ->
               if if if LLVMinfra.sumbool2bool (LLVMinfra.castop_dec co co')
                     then tv_typ t1 t1'
                     else false
                  then tv_typ t2 t2'
                  else false
               then rtv_sterm ps1 ps2 fid r st1 st1'
               else None
           | _ -> None)
    | SBSE.Coq_sterm_icmp (c, t, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_icmp (c', t', st1', st2') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.cond_dec c c')
                  then tv_typ t t'
                  else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_fcmp (c, ft, st1, st2) ->
        (match st' with
           | SBSE.Coq_sterm_fcmp (c', ft', st1', st2') ->
               if if LLVMinfra.sumbool2bool (LLVMinfra.fcond_dec c c')
                  then LLVMinfra.sumbool2bool
                         (LLVMinfra.floating_point_dec ft ft')
                  else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                      (rtv_sterm ps1 ps2 fid r st1 st1')
               else None
           | _ -> None)
    | SBSE.Coq_sterm_phi (t, stls) ->
        (match st' with
           | SBSE.Coq_sterm_phi (t', stls') ->
               if tv_typ t t'
               then rtv_list_sterm_l ps1 ps2 fid r stls stls'
               else None
           | _ -> None)
    | SBSE.Coq_sterm_select (st1, t, st2, st3) ->
        (match st' with
           | SBSE.Coq_sterm_select (st1', t', st2', st3') ->
               if tv_typ t t'
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st3 st3')
                      (mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st2 st2')
                        (rtv_sterm ps1 ps2 fid r st1 st1'))
               else None
           | _ -> None)
    | SBSE.Coq_sterm_lib (sm, i, sts) ->
        (match st' with
           | SBSE.Coq_sterm_lib (sm', i', sts') ->
               if eq_id i i'
               then mbind (fun r0 -> rtv_list_sterm ps1 ps2 fid r0 sts sts')
                      (rtv_smem ps1 ps2 fid r sm sm')
               else None
           | _ -> None)

(** val rtv_list_sz_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.list_sz_sterm -> SBSE.list_sz_sterm -> renaming option **)

and rtv_list_sz_sterm ps1 ps2 fid r sts sts' =
  match sts with
    | SBSE.Nil_list_sz_sterm ->
        (match sts' with
           | SBSE.Nil_list_sz_sterm -> Some r
           | SBSE.Cons_list_sz_sterm (s, s0, l0) -> None)
    | SBSE.Cons_list_sz_sterm (sz0, st, sts0) ->
        (match sts' with
           | SBSE.Nil_list_sz_sterm -> None
           | SBSE.Cons_list_sz_sterm (sz0', st', sts0') ->
               if LLVMinfra.sumbool2bool (LLVMsyntax.Size.dec sz0 sz0')
               then mbind (fun r0 ->
                      rtv_list_sz_sterm ps1 ps2 fid r0 sts0 sts0')
                      (rtv_sterm ps1 ps2 fid r st st')
               else None)

(** val rtv_list_sterm :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.list_sterm -> SBSE.list_sterm -> renaming option **)

and rtv_list_sterm ps1 ps2 fid r sts sts' =
  match sts with
    | SBSE.Nil_list_sterm ->
        (match sts' with
           | SBSE.Nil_list_sterm -> Some r
           | SBSE.Cons_list_sterm (s, l0) -> None)
    | SBSE.Cons_list_sterm (st, sts0) ->
        (match sts' with
           | SBSE.Nil_list_sterm -> None
           | SBSE.Cons_list_sterm (st', sts0') ->
               mbind (fun r0 -> rtv_list_sterm ps1 ps2 fid r0 sts0 sts0')
                 (rtv_sterm ps1 ps2 fid r st st'))

(** val rtv_list_sterm_l :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.id coq_AssocList -> SBSE.list_sterm_l -> SBSE.list_sterm_l ->
    renaming option **)

and rtv_list_sterm_l ps1 ps2 fid r stls stls' =
  match stls with
    | SBSE.Nil_list_sterm_l ->
        (match stls' with
           | SBSE.Nil_list_sterm_l -> Some r
           | SBSE.Cons_list_sterm_l (s, l0, l1) -> None)
    | SBSE.Cons_list_sterm_l (st, l0, stls0) ->
        (match stls' with
           | SBSE.Nil_list_sterm_l -> None
           | SBSE.Cons_list_sterm_l (st', l', stls0') ->
               if LLVMinfra.sumbool2bool (LLVMinfra.l_dec l0 l')
               then mbind (fun r0 ->
                      rtv_list_sterm_l ps1 ps2 fid r0 stls0 stls0')
                      (rtv_sterm ps1 ps2 fid r st st')
               else None)

(** val rtv_smem :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.id coq_AssocList -> SBSE.smem -> SBSE.smem -> renaming option **)

and rtv_smem ps1 ps2 fid r sm1 sm2 =
  match sm1 with
    | SBSE.Coq_smem_init -> Some r
    | SBSE.Coq_smem_malloc (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_malloc (sm4, t2, st2, a2) ->
               if if tv_typ t1 t2 then tv_align a1 a2 else false
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st1 st2)
                      (rtv_smem ps1 ps2 fid r sm3 sm4)
               else None
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               rtv_smem ps1 ps2 fid r sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if load_from_metadata sm4 st2
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if store_to_ret ps1 ps2 (rename_fid fid) st22
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | _ -> None)
    | SBSE.Coq_smem_free (sm3, t1, st1) ->
        (match sm2 with
           | SBSE.Coq_smem_free (sm4, t2, st2) ->
               if tv_typ t1 t2
               then mbind (fun r0 -> rtv_sterm ps1 ps2 fid r0 st1 st2)
                      (rtv_smem ps1 ps2 fid r sm3 sm4)
               else None
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               rtv_smem ps1 ps2 fid r sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if load_from_metadata sm4 st2
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if store_to_ret ps1 ps2 (rename_fid fid) st22
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | _ -> None)
    | SBSE.Coq_smem_alloca (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               if if tv_typ t1 t2 then tv_align a1 a2 else false
               then mbind (fun r0 -> rtv_smem ps1 ps2 fid r0 sm3 sm4)
                      (rtv_sterm ps1 ps2 fid r st1 st2)
               else rtv_smem ps1 ps2 fid r (SBSE.Coq_smem_alloca (sm3, t1,
                      st1, a1)) sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if load_from_metadata sm4 st2
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if store_to_ret ps1 ps2 (rename_fid fid) st22
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | _ -> None)
    | SBSE.Coq_smem_load (sm3, t1, st1, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               rtv_smem ps1 ps2 fid r sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if if tv_typ t1 t2 then tv_align a1 a2 else false
               then mbind (fun r0 -> rtv_smem ps1 ps2 fid r0 sm3 sm4)
                      (rtv_sterm ps1 ps2 fid r st1 st2)
               else if load_from_metadata sm4 st2
                    then rtv_smem ps1 ps2 fid r (SBSE.Coq_smem_load (sm3, t1,
                           st1, a1)) sm4
                    else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if store_to_ret ps1 ps2 (rename_fid fid) st22
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | _ -> None)
    | SBSE.Coq_smem_store (sm3, t1, st11, st12, a1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               rtv_smem ps1 ps2 fid r sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if load_from_metadata sm4 st2
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if if tv_typ t1 t2 then tv_align a1 a2 else false
               then mbind (fun r0 ->
                      mbind (fun r1 -> rtv_smem ps1 ps2 fid r1 sm3 sm4)
                        (rtv_sterm ps1 ps2 fid r0 st12 st22))
                      (rtv_sterm ps1 ps2 fid r st11 st21)
               else if store_to_ret ps1 ps2 (rename_fid fid) st22
                    then rtv_smem ps1 ps2 fid r (SBSE.Coq_smem_store (sm3,
                           t1, st11, st12, a1)) sm4
                    else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if smem_lib_sub lid
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | _ -> None)
    | SBSE.Coq_smem_lib (sm3, fid1, sts1) ->
        (match sm2 with
           | SBSE.Coq_smem_alloca (sm4, t2, st2, a2) ->
               rtv_smem ps1 ps2 fid r sm1 sm4
           | SBSE.Coq_smem_load (sm4, t2, st2, a2) ->
               if load_from_metadata sm4 st2
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_store (sm4, t2, st21, st22, a2) ->
               if store_to_ret ps1 ps2 (rename_fid fid) st22
               then rtv_smem ps1 ps2 fid r sm1 sm4
               else None
           | SBSE.Coq_smem_lib (sm4, lid, sts) ->
               if eq_id fid1 lid
               then mbind (fun r0 -> rtv_smem ps1 ps2 fid r0 sm3 sm4)
                      (rtv_list_sterm ps1 ps2 fid r sts1 sts)
               else rtv_smem ps1 ps2 fid r (SBSE.Coq_smem_lib (sm3, fid1,
                      sts1)) sm4
           | _ -> None)

(** val rtv_sframe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.sframe -> SBSE.sframe -> renaming option **)

let rec rtv_sframe ps1 ps2 fid r sf1 sf2 =
  match sf1 with
    | SBSE.Coq_sframe_init -> Some r
    | SBSE.Coq_sframe_alloca (sm1, sf3, t1, st1, a1) ->
        (match sf2 with
           | SBSE.Coq_sframe_init -> None
           | SBSE.Coq_sframe_alloca (sm2, sf4, t2, st2, a2) ->
               if if tv_typ t1 t2 then tv_align a1 a2 else false
               then mbind (fun r0 ->
                      mbind (fun r1 -> rtv_sframe ps1 ps2 fid r1 sf3 sf4)
                        (rtv_sterm ps1 ps2 fid r0 st1 st2))
                      (rtv_smem ps1 ps2 fid r sm1 sm2)
               else rtv_sframe ps1 ps2 fid r (SBSE.Coq_sframe_alloca (sm1,
                      sf3, t1, st1, a1)) sf4)

(** val match_smap :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    LLVMsyntax.id coq_AssocList -> LLVMsyntax.id -> SBSE.sterm ->
    (LLVMsyntax.id*SBSE.sterm) list -> renaming option **)

let rec match_smap ps1 ps2 fid r id1 st1 = function
  | [] -> None
  | y::sm2' ->
      let id2,st2 = y in
      (match rtv_sterm ps1 ps2 fid r st1 st2 with
         | Some r' -> Some ((id1,id2)::r')
         | None -> match_smap ps1 ps2 fid r id1 st1 sm2')

(** val rtv_smap :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.smap -> SBSE.smap -> renaming option **)

let rec rtv_smap ps1 ps2 fid r sm1 sm2 =
  match sm1 with
    | [] -> Some r
    | p::sm1' ->
        let id1,st1 = p in
        (match lookup_renaming r id1 with
           | Some id2 ->
               (match lookupAL sm2 id2 with
                  | Some st2 ->
                      mbind (fun r0 -> rtv_smap ps1 ps2 fid r0 sm1' sm2)
                        (rtv_sterm ps1 ps2 fid r st1 st2)
                  | None -> None)
           | None ->
               mbind (fun r' -> rtv_smap ps1 ps2 fid r' sm1' sm2)
                 (match_smap ps1 ps2 fid r id1 st1 sm2))

(** val rsub_sstate :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.sstate -> SBSE.sstate -> renaming option **)

let rsub_sstate ps1 ps2 fid r s1 s2 =
  if LLVMinfra.sumbool2bool
       (SBSE.sterms_dec s1.SBSE.coq_SEffects s2.SBSE.coq_SEffects)
  then mbind (fun r0 ->
         mbind (fun r1 ->
           rtv_sframe ps1 ps2 fid r1 s1.SBSE.coq_SFrame s2.SBSE.coq_SFrame)
           (rtv_smem ps1 ps2 fid r0 s1.SBSE.coq_SMem s2.SBSE.coq_SMem))
         (rtv_smap ps1 ps2 fid r s1.SBSE.coq_STerms s2.SBSE.coq_STerms)
  else None

(** val rtv_cmds :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.nbranch list -> SBSE.nbranch list -> renaming option **)

let rtv_cmds ps1 ps2 fid r nbs1 nbs2 =
  rsub_sstate ps1 ps2 fid r (SBSE.se_cmds SBSE.sstate_init nbs1)
    (SBSE.se_cmds SBSE.sstate_init nbs2)

(** val rtv_sparams :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list ->
    ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> renaming
    option **)

let rec rtv_sparams ps1 ps2 fid r tsts1 tsts2 =
  match tsts1 with
    | [] -> Some r
    | p::tsts1' ->
        let p0,st1 = p in
        let t1,a = p0 in
        (match tsts2 with
           | [] -> None
           | p1::tsts2' ->
               let p2,st2 = p1 in
               let t2,a0 = p2 in
               if tv_typ t1 t2
               then mbind (fun r0 ->
                      rtv_sparams ps1 ps2 fid r0 tsts1' tsts2')
                      (rtv_sterm ps1 ps2 fid r st1 st2)
               else None)

(** val rtv_scall :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    scall -> sicall -> renaming option **)

let rtv_scall ps1 ps2 fid r c1 c2 =
  let Coq_stmn_call (rid1, nr1, c, ty1, t1, tsts1) = c1 in
  (match c2 with
     | Coq_stmn_icall_nptr (rid2, nr2, c0, ty2, t2, tsts2) ->
         if if LLVMinfra.sumbool2bool (LLVMinfra.noret_dec nr1 nr2)
            then tv_typ ty1 ty2
            else false
         then mbind (fun r0 ->
                mbind (fun r1 -> Some ((rid1,rid2)::r1))
                  (rtv_sterm ps1 ps2 fid r0 (remove_cast t1)
                    (remove_cast t2)))
                (rtv_sparams ps1 ps2 fid r tsts1 tsts2)
         else None
     | Coq_stmn_icall_ptr
         (i, n, c0, ty2, t2, tsts2, i0, i1, rid2, i2, i3, i4, i5, c3, c4, c5) ->
         (match ty1 with
            | LLVMsyntax.Coq_typ_pointer t ->
                if tv_typ ty1 ty2
                then mbind (fun r0 ->
                       let st1 = remove_cast t1 in
                       let st2 = remove_cast t2 in
                       (match st1 with
                          | SBSE.Coq_sterm_val v ->
                              (match v with
                                 | LLVMsyntax.Coq_value_id i6 ->
                                     mbind (fun r1 -> Some ((rid1,rid2)::r1))
                                       (rtv_sterm ps1 ps2 fid r0 st1 st2)
                                 | LLVMsyntax.Coq_value_const c6 ->
                                     (match c6 with
                                        | LLVMsyntax.Coq_const_gid
                                            (t0, fid1) ->
                                            (match st2 with
                                               | SBSE.Coq_sterm_val v0 ->
                                                  (match v0 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i6 ->
                                                  mbind (fun r1 -> Some
                                                  ((rid1,rid2)::r1))
                                                  (rtv_sterm ps1 ps2 fid r0
                                                  st1 st2)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c7 ->
                                                  (match c7 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t3, fid2) ->
                                                  if tv_fid fid1 fid2
                                                  then Some ((rid1,rid2)::r0)
                                                  else None
                                                    | 
                                                  _ ->
                                                  mbind (fun r1 -> Some
                                                  ((rid1,rid2)::r1))
                                                  (rtv_sterm ps1 ps2 fid r0
                                                  st1 st2)))
                                               | _ ->
                                                  mbind (fun r1 -> Some
                                                  ((rid1,rid2)::r1))
                                                  (rtv_sterm ps1 ps2 fid r0
                                                  st1 st2))
                                        | _ ->
                                            mbind (fun r1 -> Some
                                              ((rid1,rid2)::r1))
                                              (rtv_sterm ps1 ps2 fid r0 st1
                                                st2)))
                          | _ ->
                              mbind (fun r1 -> Some ((rid1,rid2)::r1))
                                (rtv_sterm ps1 ps2 fid r0 st1 st2)))
                       (rtv_sparams ps1 ps2 fid r tsts1 tsts2)
                else None
            | _ -> None))

(** val rtv_subblock :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.subblock -> SBsyntax.subblock -> renaming option **)

let rtv_subblock ps1 ps2 fid r sb1 sb2 =
  let { SBSE.coq_NBs = nbs1; SBSE.call_cmd = call1 } = sb1 in
  let { SBsyntax.coq_NBs = nbs2; SBsyntax.call_cmd = call2 } = sb2 in
  let st1 = SBSE.se_cmds SBSE.sstate_init nbs1 in
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  let cl1 = se_call st1 call1 in
  let cl2 = se_icall st2 call2 in
  mbind (fun r0 -> rtv_scall ps1 ps2 fid r0 cl1 cl2)
    (rsub_sstate ps1 ps2 fid r st1 st2)

(** val rtv_subblocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    SBSE.subblock list -> SBsyntax.subblock list -> renaming option **)

let rec rtv_subblocks ps1 ps2 fid r sbs1 sbs2 =
  match sbs1 with
    | [] -> (match sbs2 with
               | [] -> Some r
               | s::l0 -> None)
    | sb1::sbs1' ->
        (match sbs2 with
           | [] -> None
           | sb2::sbs2' ->
               mbind (fun r0 -> rtv_subblocks ps1 ps2 fid r0 sbs1' sbs2')
                 (rtv_subblock ps1 ps2 fid r sb1 sb2))

(** val rtv_list_value_l :
    renaming -> LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l ->
    renaming option **)

let rec rtv_list_value_l r vls1 vls2 =
  match vls1 with
    | LLVMsyntax.Nil_list_value_l ->
        (match vls2 with
           | LLVMsyntax.Nil_list_value_l -> Some r
           | LLVMsyntax.Cons_list_value_l (v, l0, l1) -> None)
    | LLVMsyntax.Cons_list_value_l (v1, l1, vls3) ->
        (match vls2 with
           | LLVMsyntax.Nil_list_value_l -> None
           | LLVMsyntax.Cons_list_value_l (v2, l2, vls4) ->
               if eq_l l1 l2
               then mbind (fun r0 -> rtv_list_value_l r0 vls3 vls4)
                      (rtv_value r v1 v2)
               else None)

(** val rtv_phinode :
    renaming -> LLVMsyntax.typ -> LLVMsyntax.list_value_l -> LLVMsyntax.typ
    -> LLVMsyntax.list_value_l -> renaming option **)

let rtv_phinode r t1 vls1 t2 vls2 =
  if tv_typ t1 t2 then rtv_list_value_l r vls1 vls2 else None

(** val match_phinodes :
    renaming -> LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_value_l ->
    LLVMsyntax.phinode list -> (LLVMsyntax.phinodes*renaming) option **)

let rec match_phinodes r i1 t1 vls1 = function
  | [] -> None
  | y::ps2' ->
      let LLVMsyntax.Coq_insn_phi (i2, t2, vls2) = y in
      if is_tmp_var i2
      then (match rtv_phinode r t1 vls1 t2 vls2 with
              | Some r' -> Some (ps2',((i1,i2)::r'))
              | None -> match_phinodes r i1 t1 vls1 ps2')
      else match_phinodes r i1 t1 vls1 ps2'

(** val rtv_phinodes :
    renaming -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes -> renaming option **)

let rec rtv_phinodes r ps1 ps2 =
  match ps1 with
    | [] -> Some r
    | p::ps1' ->
        let LLVMsyntax.Coq_insn_phi (i1, t1, vls1) = p in
        (match lookup_renaming r i1 with
           | Some i2 ->
               (match lookupPhinode ps2 i2 with
                  | Some p0 ->
                      let LLVMsyntax.Coq_insn_phi (i, t2, vls2) = p0 in
                      mbind (fun r' -> rtv_phinodes r ps1' ps2)
                        (rtv_phinode r t1 vls1 t2 vls2)
                  | None -> None)
           | None ->
               (match match_phinodes r i1 t1 vls1 ps2 with
                  | Some p0 -> let ps2',r' = p0 in rtv_phinodes r' ps1' ps2'
                  | None -> None))

(** val rtv_terminator :
    LLVMsyntax.id coq_AssocList -> LLVMsyntax.terminator ->
    LLVMsyntax.terminator -> renaming option **)

let rtv_terminator r tmn1 tmn2 =
  match tmn1 with
    | LLVMsyntax.Coq_insn_return (id1, t1, v1) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return (id2, t2, v2) ->
               if tv_typ t1 t2 then rtv_value r v1 v2 else None
           | _ -> None)
    | LLVMsyntax.Coq_insn_return_void id1 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_return_void id2 -> Some r
           | _ -> None)
    | LLVMsyntax.Coq_insn_br (id1, v1, l11, l12) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br (id2, v2, l21, l22) ->
               if if eq_l l11 l21 then eq_l l12 l22 else false
               then rtv_value r v1 v2
               else None
           | _ -> None)
    | LLVMsyntax.Coq_insn_br_uncond (id1, l1) ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_br_uncond (id2, l2) ->
               if eq_l l1 l2 then Some r else None
           | _ -> None)
    | LLVMsyntax.Coq_insn_unreachable id1 ->
        (match tmn2 with
           | LLVMsyntax.Coq_insn_unreachable id2 -> Some r
           | _ -> None)

(** val rtv_block :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    LLVMsyntax.block -> SBsyntax.block -> renaming option **)

let rtv_block ps1 ps2 fid r b1 b2 =
  let LLVMsyntax.Coq_block_intro (l1, ps3, cs1, tmn1) = b1 in
  (match b2 with
     | SBsyntax.Coq_block_common (l2, ps4, sbs2, nbs2, tmn2) ->
         let sbs1,nbs1 = SBSE.cmds2sbs cs1 in
         if eq_l l1 l2
         then mbind (fun r0 ->
                mbind (fun r1 ->
                  mbind (fun r2 -> rtv_terminator r2 tmn1 tmn2)
                    (rtv_cmds ps1 ps2 fid r1 nbs1 nbs2))
                  (rtv_subblocks ps1 ps2 fid r0 sbs1 sbs2))
                (rtv_phinodes r ps3 ps4)
         else None
     | SBsyntax.Coq_block_ret_ptr (l2, ps4, sbs2, nbs2, i) ->
         let SBsyntax.Coq_insn_return_ptr
           (i0, t, i1, i2, i3, v, i4, i5, v0, i6, vp, i7, c, c0, c1) = i
         in
         let sbs1,nbs1 = SBSE.cmds2sbs cs1 in
         if eq_l l1 l2
         then mbind (fun r0 ->
                mbind (fun r1 ->
                  mbind (fun r2 ->
                    match tmn1 with
                      | LLVMsyntax.Coq_insn_return (
                          id1, t0, v1) -> rtv_value r2 v1 vp
                      | _ -> None) (rtv_cmds ps1 ps2 fid r1 nbs1 nbs2))
                  (rtv_subblocks ps1 ps2 fid r0 sbs1 sbs2))
                (rtv_phinodes r ps3 ps4)
         else None)

(** val rtv_blocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> renaming ->
    LLVMsyntax.blocks -> SBsyntax.blocks -> renaming option **)

let rec rtv_blocks ps1 ps2 fid r bs1 bs2 =
  match bs1 with
    | [] -> (match bs2 with
               | [] -> Some r
               | b::l0 -> None)
    | b1::bs1' ->
        (match bs2 with
           | [] -> None
           | b2::bs2' ->
               mbind (fun r0 -> rtv_blocks ps1 ps2 fid r0 bs1' bs2')
                 (rtv_block ps1 ps2 fid r b1 b2))

(** val rtv_fdef :
    LLVMsyntax.namedt list -> LLVMsyntax.products -> SBsyntax.products ->
    LLVMsyntax.fdef -> SBsyntax.fdef -> bool **)

let rtv_fdef nts1 ps1 ps2 f1 f2 =
  let LLVMsyntax.Coq_fdef_intro (fh1, lb1) = f1 in
  let LLVMsyntax.Coq_fheader_intro (f, t, fid1, a, v) = fh1 in
  let fh2 = LLVMsyntax.Coq_fheader_intro (f, t, fid1, a, v) in
  let SBsyntax.Coq_fdef_intro (fh3, lb2) = f2 in
  (match rtv_blocks ps1 ps2 fid1 [] lb1 lb2 with
     | Some r -> tv_fheader nts1 fh2 fh3
     | None -> false)

(** val rtv_products :
    LLVMsyntax.namedt list -> LLVMsyntax.products -> LLVMsyntax.products ->
    SBsyntax.products -> bool **)

let rec rtv_products nts1 ps10 ps1 ps2 =
  match ps1 with
    | [] -> true
    | p::ps1' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar gv1 ->
               (match SBsyntax.lookupGvarViaIDFromProducts ps2
                        (LLVMinfra.getGvarID gv1) with
                  | Some gv2 ->
                      if LLVMinfra.sumbool2bool (LLVMinfra.gvar_dec gv1 gv2)
                      then rtv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false)
           | LLVMsyntax.Coq_product_fdec f1 ->
               (match SBsyntax.lookupFdecViaIDFromProducts ps2
                        (rename_fid (LLVMinfra.getFdecID f1)) with
                  | Some f2 ->
                      if tv_fdec nts1 f1 f2
                      then rtv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false)
           | LLVMsyntax.Coq_product_fdef f1 ->
               (match SBsyntax.lookupFdefViaIDFromProducts ps2
                        (rename_fid (LLVMinfra.getFdefID f1)) with
                  | Some f2 ->
                      if rtv_fdef nts1 ps10 ps2 f1 f2
                      then rtv_products nts1 ps10 ps1' ps2
                      else false
                  | None -> false))

(** val rtv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool **)

let rtv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (los1, nts1, ps1) = m1 in
  let SBsyntax.Coq_module_intro (los2, nts2, ps2) = m2 in
  if if LLVMinfra.sumbool2bool (LLVMinfra.layouts_dec los1 los2)
     then LLVMinfra.sumbool2bool (LLVMinfra.namedts_dec nts1 nts2)
     else false
  then rtv_products nts1 ps1 ps1 ps2
  else false

(** val deref_from_metadata :
    LLVMsyntax.id -> SBSE.smem -> SBSE.sterm -> SBSE.sterm -> SBSE.sterm ->
    bool **)

let rec deref_from_metadata fid sm addr_of_b addr_of_e ptr =
  match sm with
    | SBSE.Coq_smem_malloc (sm1, t, s, a) ->
        deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | SBSE.Coq_smem_alloca (sm1, t, s, a) ->
        deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | SBSE.Coq_smem_load (sm1, t, s, a) ->
        deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | SBSE.Coq_smem_store (sm1, t, s, s0, a) ->
        deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | SBSE.Coq_smem_lib (sm1, fid1, sts1) ->
        if is_hashLoadBaseBound fid1
        then (match sts1 with
                | SBSE.Nil_list_sterm ->
                    deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
                | SBSE.Cons_list_sterm (addr_of_ptr, l0) ->
                    (match l0 with
                       | SBSE.Nil_list_sterm ->
                           deref_from_metadata fid sm1 addr_of_b addr_of_e
                             ptr
                       | SBSE.Cons_list_sterm (addr_of_base, l1) ->
                           (match l1 with
                              | SBSE.Nil_list_sterm ->
                                  deref_from_metadata fid sm1 addr_of_b
                                    addr_of_e ptr
                              | SBSE.Cons_list_sterm (
                                  addr_of_bound, l2) ->
                                  (match l2 with
                                     | SBSE.Nil_list_sterm ->
                                         deref_from_metadata fid sm1
                                           addr_of_b addr_of_e ptr
                                     | SBSE.Cons_list_sterm (
                                         s, l3) ->
                                         (match l3 with
                                            | SBSE.Nil_list_sterm ->
                                                deref_from_metadata fid sm1
                                                  addr_of_b addr_of_e ptr
                                            | SBSE.Cons_list_sterm
                                                (s0, l4) ->
                                                (match l4 with
                                                   | 
                                                 SBSE.Nil_list_sterm ->
                                                  deref_from_metadata fid sm1
                                                  addr_of_b addr_of_e ptr
                                                   | 
                                                 SBSE.Cons_list_sterm
                                                  (s1, l5) ->
                                                  (match l5 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  if 
                                                  if 
                                                  eq_sterm_upto_cast
                                                  addr_of_b addr_of_base
                                                  then 
                                                  eq_sterm_upto_cast
                                                  addr_of_e addr_of_bound
                                                  else false
                                                  then 
                                                  let st1 =
                                                  remove_cast addr_of_ptr
                                                  in
                                                  let s2 = remove_cast ptr in
                                                  (
                                                  match s2 with
                                                    | 
                                                  SBSE.Coq_sterm_load
                                                  (s3, t, st2, a) ->
                                                  eq_sterm_upto_cast st1 st2
                                                    | 
                                                  _ -> false)
                                                  else 
                                                  deref_from_metadata fid sm1
                                                  addr_of_b addr_of_e ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s2, l6) ->
                                                  deref_from_metadata fid sm1
                                                  addr_of_b addr_of_e ptr)))))))
        else deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | _ -> false

type metadata =
  ((((((LLVMsyntax.id*LLVMsyntax.l)*nat)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*bool)
  list

(** val is_metadata_aux :
    metadata -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> bool -> bool **)

let rec is_metadata_aux ms fid l1 i b e p im =
  match ms with
    | [] -> false
    | p0::ms' ->
        let p1,im' = p0 in
        let p2,p' = p1 in
        let p3,e' = p2 in
        let p4,b' = p3 in
        let p5,i' = p4 in
        let fid',l2 = p5 in
        if if if if if if if eq_id fid fid' then eq_l l1 l2 else false
                       then beq_nat i i'
                       else false
                    then eq_id b b'
                    else false
                 then eq_id e e'
                 else false
              then eq_id p p'
              else false
           then eqb im im'
           else false
        then true
        else is_metadata_aux ms' fid l1 i b e p im

(** val get_metadata : unit -> metadata **)

let get_metadata = Symexe_aux.get_metadata

(** val is_metadata :
    LLVMsyntax.id -> LLVMsyntax.l -> nat -> LLVMsyntax.id -> LLVMsyntax.id ->
    LLVMsyntax.id -> bool -> bool **)

let is_metadata fid l1 i b e p im =
  is_metadata_aux (get_metadata ()) fid l1 i b e p im

(** val check_mptr_metadata_aux :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm
    -> SBSE.sterm -> SBSE.sterm -> bool **)

let rec check_mptr_metadata_aux ps2 fid l1 i base bound ptr =
  let p = base,bound in
  let st1,y = p in
  (match st1 with
     | SBSE.Coq_sterm_val v ->
         (match v with
            | LLVMsyntax.Coq_value_id idb ->
                (match y with
                   | SBSE.Coq_sterm_val v0 ->
                       (match v0 with
                          | LLVMsyntax.Coq_value_id ide ->
                              (match ptr with
                                 | SBSE.Coq_sterm_val v1 ->
                                     (match v1 with
                                        | LLVMsyntax.Coq_value_id idp ->
                                            is_metadata fid l1 i idb ide idp
                                              true
                                        | LLVMsyntax.Coq_value_const c ->
                                            false)
                                 | _ -> false)
                          | LLVMsyntax.Coq_value_const c -> false)
                   | _ -> false)
            | LLVMsyntax.Coq_value_const c1 ->
                (match c1 with
                   | LLVMsyntax.Coq_const_undef t ->
                       (match y with
                          | SBSE.Coq_sterm_val v0 ->
                              (match v0 with
                                 | LLVMsyntax.Coq_value_id i0 -> false
                                 | LLVMsyntax.Coq_value_const c ->
                                     (match c with
                                        | LLVMsyntax.Coq_const_undef t0 ->
                                            (match ptr with
                                               | SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i0 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c0 ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_const_undef
                                                  t1 -> true
                                                    | 
                                                  _ -> false))
                                               | _ -> false)
                                        | _ -> false))
                          | _ -> false)
                   | LLVMsyntax.Coq_const_null t0 ->
                       (match y with
                          | SBSE.Coq_sterm_val v0 ->
                              (match v0 with
                                 | LLVMsyntax.Coq_value_id i0 -> false
                                 | LLVMsyntax.Coq_value_const c ->
                                     (match c with
                                        | LLVMsyntax.Coq_const_null t ->
                                            (match ptr with
                                               | SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i0 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c0 ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_const_null
                                                  t1 -> true
                                                    | 
                                                  _ -> false))
                                               | SBSE.Coq_sterm_cast
                                                  (c0, t1, s, t2) ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_castop_inttoptr ->
                                                  true
                                                    | 
                                                  _ -> false)
                                               | _ -> false)
                                        | LLVMsyntax.Coq_const_castop
                                            (c0, c2, t1) ->
                                            (match c0 with
                                               | LLVMsyntax.Coq_castop_inttoptr ->
                                                  (match c2 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s, i0) ->
                                                  (match ptr with
                                                    | 
                                                  SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c3 ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t, id0) ->
                                                  (match t with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t2 ->
                                                  (match t2 with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t3 ->
                                                  if 
                                                  if 
                                                  if tv_typ t0 t1
                                                  then 
                                                  tv_typ t0
                                                  (LLVMsyntax.Coq_typ_pointer
                                                  (LLVMsyntax.Coq_typ_int
                                                  LLVMsyntax.Size.coq_Eight))
                                                  else false
                                                  then 
                                                  eq_INT_Z i0
                                                  (two_p (Zpos (Coq_xO
                                                  (Coq_xO (Coq_xO (Coq_xO
                                                  (Coq_xI Coq_xH)))))))
                                                  else false
                                                  then 
                                                  (match 
                                                  SBsyntax.lookupGvarFromProducts
                                                  ps2 id0 with
                                                    | 
                                                  Some g ->
                                                  (match g with
                                                    | 
                                                  LLVMsyntax.Coq_gvar_intro
                                                  (i1, l0, g0, t4, c4, a) ->
                                                  false
                                                    | 
                                                  LLVMsyntax.Coq_gvar_external
                                                  (i1, g0, t4) -> true)
                                                    | 
                                                  None -> false)
                                                  else false
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  _ -> false)
                                               | _ -> false)
                                        | _ -> false))
                          | _ -> false)
                   | LLVMsyntax.Coq_const_gid (t, i0) ->
                       let c2 = LLVMsyntax.Coq_const_gid (t, i0) in
                       (match y with
                          | SBSE.Coq_sterm_val v0 ->
                              (match v0 with
                                 | LLVMsyntax.Coq_value_id i1 -> false
                                 | LLVMsyntax.Coq_value_const c ->
                                     (match c with
                                        | LLVMsyntax.Coq_const_gep
                                            (i1, c3, l0) ->
                                            (match c3 with
                                               | LLVMsyntax.Coq_const_gid
                                                  (t0, i2) ->
                                                  let c4 =
                                                  LLVMsyntax.Coq_const_gid
                                                  (t0, i2)
                                                  in
                                                  (
                                                  match l0 with
                                                    | 
                                                  LLVMsyntax.Nil_list_const ->
                                                  false
                                                    | 
                                                  LLVMsyntax.Cons_list_const
                                                  (c0, l2) ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s, i3) ->
                                                  (match l2 with
                                                    | 
                                                  LLVMsyntax.Nil_list_const ->
                                                  (match ptr with
                                                    | 
                                                  SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i4 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c5 ->
                                                  (match c5 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t1, i4) ->
                                                  let c6 =
                                                  LLVMsyntax.Coq_const_gid
                                                  (t1, i4)
                                                  in
                                                  if 
                                                  if eq_const c2 c4
                                                  then eq_const c2 c6
                                                  else false
                                                  then 
                                                  eq_INT_Z i3 (Zpos Coq_xH)
                                                  else false
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  LLVMsyntax.Cons_list_const
                                                  (c5, l3) -> false)
                                                    | 
                                                  _ -> false))
                                               | _ -> false)
                                        | _ -> false))
                          | _ -> false)
                   | _ -> false))
     | SBSE.Coq_sterm_malloc (s, t, st10, a) ->
         let st2 = SBSE.Coq_sterm_malloc (s, t, st10, a) in
         (match y with
            | SBSE.Coq_sterm_gep (i0, t0, st3, l0) ->
                (match l0 with
                   | SBSE.Nil_list_sz_sterm -> false
                   | SBSE.Cons_list_sz_sterm (s0, st20, l2) ->
                       (match l2 with
                          | SBSE.Nil_list_sz_sterm ->
                              (match ptr with
                                 | SBSE.Coq_sterm_malloc (
                                     s1, t1, s2, a0) ->
                                     let st4 = SBSE.Coq_sterm_malloc (s1, t1,
                                       s2, a0)
                                     in
                                     if if eq_sterm_upto_cast st2 st3
                                        then eq_sterm_upto_cast st2 st4
                                        else false
                                     then eq_sterm st10 st20
                                     else false
                                 | _ -> false)
                          | SBSE.Cons_list_sz_sterm (s1, s2, l3) -> false))
            | _ -> false)
     | SBSE.Coq_sterm_alloca (s, t, st10, a) ->
         let st2 = SBSE.Coq_sterm_alloca (s, t, st10, a) in
         (match y with
            | SBSE.Coq_sterm_gep (i0, t0, st3, l0) ->
                (match l0 with
                   | SBSE.Nil_list_sz_sterm -> false
                   | SBSE.Cons_list_sz_sterm (s0, st20, l2) ->
                       (match l2 with
                          | SBSE.Nil_list_sz_sterm ->
                              (match ptr with
                                 | SBSE.Coq_sterm_alloca (
                                     s1, t1, s2, a0) ->
                                     let st4 = SBSE.Coq_sterm_alloca (s1, t1,
                                       s2, a0)
                                     in
                                     if if eq_sterm_upto_cast st2 st3
                                        then eq_sterm_upto_cast st2 st4
                                        else false
                                     then eq_sterm st10 st20
                                     else false
                                 | _ -> false)
                          | SBSE.Cons_list_sz_sterm (s1, s2, l3) -> false))
            | _ -> false)
     | SBSE.Coq_sterm_load (sm1, t, st2, a) ->
         (match y with
            | SBSE.Coq_sterm_load (sm2, t0, st3, a0) ->
                deref_from_metadata fid sm1 st2 st3 ptr
            | _ -> false)
     | SBSE.Coq_sterm_select (st10, t, st11, st12) ->
         (match y with
            | SBSE.Coq_sterm_select (st20, t0, st21, st22) ->
                (match ptr with
                   | SBSE.Coq_sterm_select (st30, t1, st31, st32) ->
                       if if if eq_sterm st10 st20
                             then eq_sterm st20 st30
                             else false
                          then check_mptr_metadata_aux ps2 fid l1 i st11 st21
                                 st31
                          else false
                       then check_mptr_metadata_aux ps2 fid l1 i st12 st22
                              st32
                       else false
                   | _ -> false)
            | _ -> false)
     | _ -> false)

(** val check_mptr_metadata :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm
    -> SBSE.sterm -> SBSE.sterm -> bool **)

let check_mptr_metadata ps2 fid l1 i base bound ptr =
  check_mptr_metadata_aux ps2 fid l1 i (remove_cast base) 
    (remove_cast bound) (get_ptr_object ptr)

(** val check_fptr_metadata_aux :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm
    -> SBSE.sterm -> SBSE.sterm -> bool **)

let rec check_fptr_metadata_aux ps2 fid l1 i base bound ptr =
  let p = base,bound in
  let y,y0 = p in
  (match y with
     | SBSE.Coq_sterm_val v ->
         (match v with
            | LLVMsyntax.Coq_value_id idb ->
                (match y0 with
                   | SBSE.Coq_sterm_val v0 ->
                       (match v0 with
                          | LLVMsyntax.Coq_value_id ide ->
                              (match ptr with
                                 | SBSE.Coq_sterm_val v1 ->
                                     (match v1 with
                                        | LLVMsyntax.Coq_value_id idp ->
                                            is_metadata fid l1 i idb ide idp
                                              false
                                        | LLVMsyntax.Coq_value_const c ->
                                            false)
                                 | _ -> false)
                          | LLVMsyntax.Coq_value_const c -> false)
                   | _ -> false)
            | LLVMsyntax.Coq_value_const c ->
                (match c with
                   | LLVMsyntax.Coq_const_gid (t, id1) ->
                       (match y0 with
                          | SBSE.Coq_sterm_val v0 ->
                              (match v0 with
                                 | LLVMsyntax.Coq_value_id i0 -> false
                                 | LLVMsyntax.Coq_value_const c0 ->
                                     (match c0 with
                                        | LLVMsyntax.Coq_const_gid
                                            (t0, id2) ->
                                            (match ptr with
                                               | SBSE.Coq_sterm_val v1 ->
                                                  (match v1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i0 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c1 ->
                                                  (match c1 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t1, id3) ->
                                                  (match 
                                                  SBsyntax.lookupFdecFromProducts
                                                  ps2 id1 with
                                                    | 
                                                  Some f ->
                                                  if eq_id id1 id2
                                                  then eq_id id2 id3
                                                  else false
                                                    | 
                                                  None -> false)
                                                    | 
                                                  _ -> false))
                                               | _ -> false)
                                        | _ -> false))
                          | _ -> false)
                   | _ -> false))
     | SBSE.Coq_sterm_load (sm1, t, st1, a) ->
         (match y0 with
            | SBSE.Coq_sterm_load (sm2, t0, st2, a0) ->
                deref_from_metadata fid sm1 st1 st2 ptr
            | _ -> false)
     | SBSE.Coq_sterm_select (st10, t, st11, st12) ->
         (match y0 with
            | SBSE.Coq_sterm_select (st20, t0, st21, st22) ->
                (match ptr with
                   | SBSE.Coq_sterm_select (st30, t1, st31, st32) ->
                       if if if eq_sterm st10 st20
                             then eq_sterm st20 st30
                             else false
                          then check_fptr_metadata_aux ps2 fid l1 i st11 st21
                                 st31
                          else false
                       then check_fptr_metadata_aux ps2 fid l1 i st12 st22
                              st32
                       else false
                   | _ -> false)
            | _ -> false)
     | _ -> false)

(** val check_fptr_metadata :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm
    -> SBSE.sterm -> SBSE.sterm -> bool **)

let check_fptr_metadata ps2 fid l1 i base bound ptr =
  check_fptr_metadata_aux ps2 fid l1 i (remove_cast base) 
    (remove_cast bound) (remove_cast ptr)

(** val check_metadata :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.sterm
    -> SBSE.sterm -> SBSE.sterm -> bool -> bool **)

let check_metadata ps2 fid l1 i base bound ptr = function
  | true -> check_mptr_metadata ps2 fid l1 i base bound ptr
  | false -> check_fptr_metadata ps2 fid l1 i base bound ptr

(** val deref_check :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat ->
    LLVMsyntax.id -> SBSE.list_sterm -> bool **)

let deref_check ps2 fid l1 i lid sts =
  if is_loadStoreDereferenceCheck lid
  then (match sts with
          | SBSE.Nil_list_sterm -> false
          | SBSE.Cons_list_sterm (base, l0) ->
              (match l0 with
                 | SBSE.Nil_list_sterm -> false
                 | SBSE.Cons_list_sterm (bound, l2) ->
                     (match l2 with
                        | SBSE.Nil_list_sterm -> false
                        | SBSE.Cons_list_sterm (ptr, l3) ->
                            (match l3 with
                               | SBSE.Nil_list_sterm -> false
                               | SBSE.Cons_list_sterm (
                                   size_of_type, l4) ->
                                   (match l4 with
                                      | SBSE.Nil_list_sterm -> false
                                      | SBSE.Cons_list_sterm (
                                          s, l5) ->
                                          (match l5 with
                                             | SBSE.Nil_list_sterm ->
                                                 check_mptr_metadata ps2 fid
                                                  l1 i base bound ptr
                                             | SBSE.Cons_list_sterm
                                                 (s0, l6) -> false))))))
  else if is_callDereferenceCheck lid
       then (match sts with
               | SBSE.Nil_list_sterm -> false
               | SBSE.Cons_list_sterm (base, l0) ->
                   (match l0 with
                      | SBSE.Nil_list_sterm -> false
                      | SBSE.Cons_list_sterm (bound, l2) ->
                          (match l2 with
                             | SBSE.Nil_list_sterm -> false
                             | SBSE.Cons_list_sterm (
                                 ptr, l3) ->
                                 (match l3 with
                                    | SBSE.Nil_list_sterm ->
                                        check_fptr_metadata ps2 fid l1 i base
                                          bound ptr
                                    | SBSE.Cons_list_sterm (s, l4) -> false))))
       else true

(** val find_stored_ptr : SBSE.smem -> SBSE.sterm -> SBSE.sterm option **)

let rec find_stored_ptr sm addr_of_ptr =
  match sm with
    | SBSE.Coq_smem_init -> None
    | SBSE.Coq_smem_malloc (sm1, t, s, a) -> find_stored_ptr sm1 addr_of_ptr
    | SBSE.Coq_smem_free (sm1, t, s) -> find_stored_ptr sm1 addr_of_ptr
    | SBSE.Coq_smem_alloca (sm1, t, s, a) -> find_stored_ptr sm1 addr_of_ptr
    | SBSE.Coq_smem_load (sm1, t, s, a) -> find_stored_ptr sm1 addr_of_ptr
    | SBSE.Coq_smem_store (sm1, t, st1, st2, a) ->
        if eq_sterm_upto_cast st2 addr_of_ptr
        then Some st1
        else find_stored_ptr sm1 addr_of_ptr
    | SBSE.Coq_smem_lib (sm1, i, l0) -> find_stored_ptr sm1 addr_of_ptr

(** val store_to_metadata :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smem ->
    LLVMsyntax.id -> SBSE.list_sterm -> bool **)

let rec store_to_metadata ps2 fid l1 i sm lid sts =
  if is_hashLoadBaseBound lid
  then (match sts with
          | SBSE.Nil_list_sterm -> false
          | SBSE.Cons_list_sterm (addr_of_ptr, l0) ->
              (match l0 with
                 | SBSE.Nil_list_sterm -> false
                 | SBSE.Cons_list_sterm (base, l2) ->
                     (match l2 with
                        | SBSE.Nil_list_sterm -> false
                        | SBSE.Cons_list_sterm (bound, l3) ->
                            (match l3 with
                               | SBSE.Nil_list_sterm -> false
                               | SBSE.Cons_list_sterm (
                                   s, l4) ->
                                   (match l4 with
                                      | SBSE.Nil_list_sterm -> false
                                      | SBSE.Cons_list_sterm (
                                          s0, l5) ->
                                          (match l5 with
                                             | SBSE.Nil_list_sterm -> false
                                             | SBSE.Cons_list_sterm
                                                 (s1, l6) ->
                                                 (match l6 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  (match 
                                                  find_stored_ptr sm
                                                  addr_of_ptr with
                                                    | 
                                                  Some ptr ->
                                                  if 
                                                  check_mptr_metadata ps2 fid
                                                  l1 i base bound ptr
                                                  then true
                                                  else 
                                                  check_fptr_metadata ps2 fid
                                                  l1 i base bound ptr
                                                    | 
                                                  None -> false)
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s2, l7) -> false)))))))
  else true

(** val get_addrof_be :
    unit -> ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) list **)

let get_addrof_be = Symexe_aux.get_addrof_be

(** val is_addrof_be_aux :
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) list -> LLVMsyntax.id ->
    LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let rec is_addrof_be_aux abes fid ab ae =
  match abes with
    | [] -> false
    | p::abes' ->
        let p0,ae' = p in
        let fid',ab' = p0 in
        if if if eq_id fid fid' then eq_id ab ab' else false
           then eq_id ae ae'
           else false
        then true
        else is_addrof_be_aux abes' fid ab ae

(** val is_addrof_be : LLVMsyntax.id -> SBSE.sterm -> SBSE.sterm -> bool **)

let is_addrof_be fid sab sae =
  match sab with
    | SBSE.Coq_sterm_val v ->
        (match v with
           | LLVMsyntax.Coq_value_id ab ->
               (match sae with
                  | SBSE.Coq_sterm_val v0 ->
                      (match v0 with
                         | LLVMsyntax.Coq_value_id ae ->
                             is_addrof_be_aux (get_addrof_be ()) fid ab ae
                         | LLVMsyntax.Coq_value_const c -> false)
                  | _ -> false)
           | LLVMsyntax.Coq_value_const c -> false)
    | SBSE.Coq_sterm_alloca (s, t, s0, a) ->
        (match sae with
           | SBSE.Coq_sterm_alloca (s1, t0, s2, a0) -> true
           | _ -> false)
    | _ -> false

(** val safe_mem_access :
    LLVMsyntax.id -> SBSE.smem -> LLVMsyntax.typ -> SBSE.sterm -> bool **)

let rec safe_mem_access fid sm t ptr =
  match sm with
    | SBSE.Coq_smem_init -> false
    | SBSE.Coq_smem_malloc (sm1, t0, s, a) -> safe_mem_access fid sm1 t ptr
    | SBSE.Coq_smem_free (sm1, t0, s) -> safe_mem_access fid sm1 t ptr
    | SBSE.Coq_smem_alloca (sm1, t0, s, a) -> safe_mem_access fid sm1 t ptr
    | SBSE.Coq_smem_load (sm1, t0, s, a) -> safe_mem_access fid sm1 t ptr
    | SBSE.Coq_smem_store (sm1, t0, s, s0, a) ->
        safe_mem_access fid sm1 t ptr
    | SBSE.Coq_smem_lib (sm1, fid1, sts1) ->
        if is_loadStoreDereferenceCheck fid1
        then (match sts1 with
                | SBSE.Nil_list_sterm -> safe_mem_access fid sm1 t ptr
                | SBSE.Cons_list_sterm (s, l0) ->
                    (match l0 with
                       | SBSE.Nil_list_sterm -> safe_mem_access fid sm1 t ptr
                       | SBSE.Cons_list_sterm (s0, l1) ->
                           (match l1 with
                              | SBSE.Nil_list_sterm ->
                                  safe_mem_access fid sm1 t ptr
                              | SBSE.Cons_list_sterm (
                                  actual_ptr, l2) ->
                                  (match l2 with
                                     | SBSE.Nil_list_sterm ->
                                         safe_mem_access fid sm1 t ptr
                                     | SBSE.Cons_list_sterm (
                                         s1, l3) ->
                                         (match s1 with
                                            | SBSE.Coq_sterm_val v ->
                                                (match v with
                                                   | 
                                                 LLVMsyntax.Coq_value_id i ->
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                   | 
                                                 LLVMsyntax.Coq_value_const
                                                  c ->
                                                  (match c with
                                                    | 
                                                  LLVMsyntax.Coq_const_castop
                                                  (c0, c1, t0) ->
                                                  (match c0 with
                                                    | 
                                                  LLVMsyntax.Coq_castop_ptrtoint ->
                                                  (match c1 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gep
                                                  (i, c2, l4) ->
                                                  if i
                                                  then 
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                  else 
                                                  (match c2 with
                                                    | 
                                                  LLVMsyntax.Coq_const_null
                                                  t1 ->
                                                  (match l4 with
                                                    | 
                                                  LLVMsyntax.Nil_list_const ->
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                    | 
                                                  LLVMsyntax.Cons_list_const
                                                  (c3, l5) ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s2, i0) ->
                                                  (match l5 with
                                                    | 
                                                  LLVMsyntax.Nil_list_const ->
                                                  (match t0 with
                                                    | 
                                                  LLVMsyntax.Coq_typ_int
                                                  sz ->
                                                  (match l3 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s3, l6) ->
                                                  (match l6 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  if 
                                                  if 
                                                  if 
                                                  eq_sterm
                                                  (get_ptr_object ptr)
                                                  (get_ptr_object actual_ptr)
                                                  then 
                                                  eq_INT_Z i0 (Zpos Coq_xH)
                                                  else false
                                                  then 
                                                  LLVMinfra.sumbool2bool
                                                  (LLVMsyntax.Size.dec sz
                                                  LLVMsyntax.Size.coq_ThirtyTwo)
                                                  else false
                                                  then true
                                                  else 
                                                  safe_mem_access fid sm1 t1
                                                  ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s4, l7) ->
                                                  safe_mem_access fid sm1 t
                                                  ptr))
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)
                                                    | 
                                                  LLVMsyntax.Cons_list_const
                                                  (c4, l6) ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr))
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)
                                                    | 
                                                  _ ->
                                                  safe_mem_access fid sm1 t
                                                  ptr))
                                            | _ ->
                                                safe_mem_access fid sm1 t ptr)))))
        else if is_hashLoadBaseBound fid1
             then (match sts1 with
                     | SBSE.Nil_list_sterm -> safe_mem_access fid sm1 t ptr
                     | SBSE.Cons_list_sterm (s, l0) ->
                         (match l0 with
                            | SBSE.Nil_list_sterm ->
                                safe_mem_access fid sm1 t ptr
                            | SBSE.Cons_list_sterm (
                                addr_of_base, l1) ->
                                (match l1 with
                                   | SBSE.Nil_list_sterm ->
                                       safe_mem_access fid sm1 t ptr
                                   | SBSE.Cons_list_sterm
                                       (addr_of_bound, l2) ->
                                       (match l2 with
                                          | SBSE.Nil_list_sterm ->
                                              safe_mem_access fid sm1 t ptr
                                          | SBSE.Cons_list_sterm (
                                              s0, l3) ->
                                              (match l3 with
                                                 | 
                                               SBSE.Nil_list_sterm ->
                                                 safe_mem_access fid sm1 t
                                                  ptr
                                                 | 
                                               SBSE.Cons_list_sterm
                                                 (s1, l4) ->
                                                 (match l4 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (ptr_safe, l5) ->
                                                  (match l5 with
                                                    | 
                                                  SBSE.Nil_list_sterm ->
                                                  if 
                                                  if 
                                                  if 
                                                  eq_sterm ptr addr_of_base
                                                  then true
                                                  else 
                                                  eq_sterm ptr addr_of_bound
                                                  then true
                                                  else eq_sterm ptr ptr_safe
                                                  then 
                                                  is_addrof_be fid
                                                  addr_of_base addr_of_bound
                                                  else 
                                                  safe_mem_access fid sm1 t
                                                  ptr
                                                    | 
                                                  SBSE.Cons_list_sterm
                                                  (s2, l6) ->
                                                  safe_mem_access fid sm1 t
                                                  ptr)))))))
             else safe_mem_access fid sm1 t ptr

(** val sterm_is_memsafe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBSE.sterm -> bool **)

let rec sterm_is_memsafe ps1 ps2 fid l0 i = function
  | SBSE.Coq_sterm_val v -> true
  | SBSE.Coq_sterm_bop (b, s, st1, st2) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then sterm_is_memsafe ps1 ps2 fid l0 i st2
      else false
  | SBSE.Coq_sterm_fbop (f, f0, st1, st2) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then sterm_is_memsafe ps1 ps2 fid l0 i st2
      else false
  | SBSE.Coq_sterm_extractvalue (t, st1, l1) ->
      sterm_is_memsafe ps1 ps2 fid l0 i st1
  | SBSE.Coq_sterm_insertvalue (t, st1, t0, st2, l1) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then sterm_is_memsafe ps1 ps2 fid l0 i st2
      else false
  | SBSE.Coq_sterm_malloc (sm, t, st1, a) ->
      if smem_is_memsafe ps1 ps2 fid l0 i sm
      then sterm_is_memsafe ps1 ps2 fid l0 i st1
      else false
  | SBSE.Coq_sterm_alloca (sm, t, st1, a) ->
      if smem_is_memsafe ps1 ps2 fid l0 i sm
      then sterm_is_memsafe ps1 ps2 fid l0 i st1
      else false
  | SBSE.Coq_sterm_load (sm, t, st1, a) ->
      if if smem_is_memsafe ps1 ps2 fid l0 i sm
         then sterm_is_memsafe ps1 ps2 fid l0 i st1
         else false
      then safe_mem_access fid sm t st1
      else false
  | SBSE.Coq_sterm_gep (i0, t, st1, sts2) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then list_sz_sterm_is_memsafe ps1 ps2 fid l0 i sts2
      else false
  | SBSE.Coq_sterm_trunc (t, t0, st1, t1) ->
      sterm_is_memsafe ps1 ps2 fid l0 i st1
  | SBSE.Coq_sterm_ext (e, t, st1, t0) ->
      sterm_is_memsafe ps1 ps2 fid l0 i st1
  | SBSE.Coq_sterm_cast (c, t, st1, t0) ->
      sterm_is_memsafe ps1 ps2 fid l0 i st1
  | SBSE.Coq_sterm_icmp (c, t, st1, st2) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then sterm_is_memsafe ps1 ps2 fid l0 i st2
      else false
  | SBSE.Coq_sterm_fcmp (f, f0, st1, st2) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st1
      then sterm_is_memsafe ps1 ps2 fid l0 i st2
      else false
  | SBSE.Coq_sterm_phi (t, stls) ->
      list_sterm_l_is_memsafe ps1 ps2 fid l0 i stls
  | SBSE.Coq_sterm_select (st1, t, st2, st3) ->
      if if sterm_is_memsafe ps1 ps2 fid l0 i st1
         then sterm_is_memsafe ps1 ps2 fid l0 i st2
         else false
      then sterm_is_memsafe ps1 ps2 fid l0 i st3
      else false
  | SBSE.Coq_sterm_lib (sm, lid, sts) ->
      if if smem_is_memsafe ps1 ps2 fid l0 i sm
         then list_sterm_is_memsafe ps1 ps2 fid l0 i sts
         else false
      then store_to_metadata ps2 fid l0 i sm lid sts
      else false

(** val list_sz_sterm_is_memsafe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBSE.list_sz_sterm -> bool **)

and list_sz_sterm_is_memsafe ps1 ps2 fid l0 i = function
  | SBSE.Nil_list_sz_sterm -> true
  | SBSE.Cons_list_sz_sterm (s, st, sts0) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st
      then list_sz_sterm_is_memsafe ps1 ps2 fid l0 i sts0
      else false

(** val list_sterm_is_memsafe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBSE.list_sterm -> bool **)

and list_sterm_is_memsafe ps1 ps2 fid l0 i = function
  | SBSE.Nil_list_sterm -> true
  | SBSE.Cons_list_sterm (st, sts0) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st
      then list_sterm_is_memsafe ps1 ps2 fid l0 i sts0
      else false

(** val list_sterm_l_is_memsafe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBSE.list_sterm_l -> bool **)

and list_sterm_l_is_memsafe ps1 ps2 fid l0 i = function
  | SBSE.Nil_list_sterm_l -> true
  | SBSE.Cons_list_sterm_l (st, l1, stls0) ->
      if sterm_is_memsafe ps1 ps2 fid l0 i st
      then list_sterm_l_is_memsafe ps1 ps2 fid l0 i stls0
      else false

(** val smem_is_memsafe :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBSE.smem -> bool **)

and smem_is_memsafe ps1 ps2 fid l0 i = function
  | SBSE.Coq_smem_init -> true
  | SBSE.Coq_smem_malloc (sm1, t, st1, a) ->
      if smem_is_memsafe ps1 ps2 fid l0 i sm1
      then sterm_is_memsafe ps1 ps2 fid l0 i st1
      else false
  | SBSE.Coq_smem_free (sm1, t, s) -> false
  | SBSE.Coq_smem_alloca (sm1, t, st1, a) ->
      if smem_is_memsafe ps1 ps2 fid l0 i sm1
      then sterm_is_memsafe ps1 ps2 fid l0 i st1
      else false
  | SBSE.Coq_smem_load (sm1, t, st1, a) ->
      if if smem_is_memsafe ps1 ps2 fid l0 i sm1
         then sterm_is_memsafe ps1 ps2 fid l0 i st1
         else false
      then safe_mem_access fid sm1 t st1
      else false
  | SBSE.Coq_smem_store (sm1, t, st11, st12, a) ->
      if if if smem_is_memsafe ps1 ps2 fid l0 i sm1
            then sterm_is_memsafe ps1 ps2 fid l0 i st11
            else false
         then sterm_is_memsafe ps1 ps2 fid l0 i st12
         else false
      then if store_to_ret ps1 ps2 fid st12
           then true
           else safe_mem_access fid sm1 (LLVMsyntax.Coq_typ_pointer t) st12
      else false
  | SBSE.Coq_smem_lib (sm1, lid1, sts1) ->
      if if smem_is_memsafe ps1 ps2 fid l0 i sm1
         then list_sterm_is_memsafe ps1 ps2 fid l0 i sts1
         else false
      then deref_check ps2 fid l0 i lid1 sts1
      else false

(** val check_all_metadata_aux :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smap ->
    metadata -> bool **)

let rec check_all_metadata_aux ps2 fid l1 i1 sm = function
  | [] -> true
  | p0::ms' ->
      let p1,im = p0 in
      let p2,p = p1 in
      let p3,e = p2 in
      let p4,b = p3 in
      let p5,i2 = p4 in
      let fid0,l2 = p5 in
      if if if if eq_id fid0 fid then eq_l l1 l2 else false
            then beq_nat i1 i2
            else false
         then let p6 = (lookupAL sm b),(lookupAL sm e) in
              let o = lookupAL sm p in
              let o0,o1 = p6 in
              (match o0 with
                 | Some sb ->
                     (match o1 with
                        | Some se ->
                            (match o with
                               | Some sp ->
                                   check_metadata ps2 fid l1 i1 sb se sp im
                               | None ->
                                   check_metadata ps2 fid l1 i1 sb se
                                     (SBSE.Coq_sterm_val
                                     (LLVMsyntax.Coq_value_id p)) im)
                        | None -> false)
                 | None ->
                     (match o1 with
                        | Some s -> false
                        | None ->
                            (match o with
                               | Some s ->
                                   (match s with
                                      | SBSE.Coq_sterm_gep (
                                          i, t, s0, l0) -> true
                                      | _ -> false)
                               | None -> true)))
         else true
      then check_all_metadata_aux ps2 fid l1 i1 sm ms'
      else false

(** val check_all_metadata :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smap ->
    bool **)

let check_all_metadata ps2 fid l0 i sm =
  check_all_metadata_aux ps2 fid l0 i sm (get_metadata ())

(** val check_addrof_be_aux :
    LLVMsyntax.id -> SBSE.smap ->
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) list -> bool **)

let rec check_addrof_be_aux fid sm = function
  | [] -> true
  | p::abes' ->
      let p0,ae = p in
      let fid0,ab = p0 in
      if if eq_id fid0 fid
         then let o = lookupAL sm ab in
              let o0 = lookupAL sm ae in
              (match o with
                 | Some s ->
                     (match s with
                        | SBSE.Coq_sterm_alloca (s0, t, s1, a) ->
                            (match o0 with
                               | Some s2 ->
                                   (match s2 with
                                      | SBSE.Coq_sterm_alloca
                                          (s3, t0, s4, a0) -> true
                                      | _ -> false)
                               | None -> false)
                        | _ -> false)
                 | None -> (match o0 with
                              | Some s -> false
                              | None -> true))
         else true
      then check_addrof_be_aux fid sm abes'
      else false

(** val check_addrof_be : LLVMsyntax.id -> SBSE.smap -> bool **)

let check_addrof_be fid sm =
  check_addrof_be_aux fid sm (get_addrof_be ())

(** val mtv_cmds :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> SBSE.nbranch list -> bool **)

let mtv_cmds ps1 ps2 fid l0 nbs2 =
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  if if smem_is_memsafe ps1 ps2 fid l0 O st2.SBSE.coq_SMem
     then check_all_metadata ps2 fid l0 O st2.SBSE.coq_STerms
     else false
  then check_addrof_be fid st2.SBSE.coq_STerms
  else false

(** val mtv_func_metadata :
    metadata -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat ->
    LLVMsyntax.id -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.id)
    list -> ((LLVMsyntax.typ*LLVMsyntax.attributes)*SBSE.sterm) list -> bool **)

let rec mtv_func_metadata ms ps2 fid l1 i1 fid2 ars2 sars2 =
  match ms with
    | [] -> true
    | p0::ms' ->
        let p1,im = p0 in
        let p2,p = p1 in
        let p3,e = p2 in
        let p4,b = p3 in
        let p5,i2 = p4 in
        let fid0,l2 = p5 in
        if if if if eq_id fid0 fid2 then eq_l l2 (l_of_arg ()) else false
              then beq_nat i2 O
              else false
           then let p6 = (lookupSarg ars2 sars2 b),(lookupSarg ars2 sars2 e)
                in
                let o = lookupSarg ars2 sars2 p in
                let o0,o1 = p6 in
                (match o0 with
                   | Some sb ->
                       (match o1 with
                          | Some se ->
                              (match o with
                                 | Some sp ->
                                     check_metadata ps2 fid l1 i1 sb se sp im
                                 | None -> false)
                          | None -> false)
                   | None -> false)
           else true
        then mtv_func_metadata ms' ps2 fid l1 i1 fid2 ars2 sars2
        else false

(** val safe_fptr_access_aux : SBSE.smem -> SBSE.sterm -> bool **)

let rec safe_fptr_access_aux sm ptr =
  match sm with
    | SBSE.Coq_smem_init -> false
    | SBSE.Coq_smem_malloc (sm1, t, s, a) -> safe_fptr_access_aux sm1 ptr
    | SBSE.Coq_smem_free (sm1, t, s) -> safe_fptr_access_aux sm1 ptr
    | SBSE.Coq_smem_alloca (sm1, t, s, a) -> safe_fptr_access_aux sm1 ptr
    | SBSE.Coq_smem_load (sm1, t, s, a) -> safe_fptr_access_aux sm1 ptr
    | SBSE.Coq_smem_store (sm1, t, s, s0, a) -> safe_fptr_access_aux sm1 ptr
    | SBSE.Coq_smem_lib (sm1, fid1, sts1) ->
        if is_callDereferenceCheck fid1
        then (match sts1 with
                | SBSE.Nil_list_sterm -> safe_fptr_access_aux sm1 ptr
                | SBSE.Cons_list_sterm (s, l0) ->
                    (match l0 with
                       | SBSE.Nil_list_sterm -> safe_fptr_access_aux sm1 ptr
                       | SBSE.Cons_list_sterm (s0, l1) ->
                           (match l1 with
                              | SBSE.Nil_list_sterm ->
                                  safe_fptr_access_aux sm1 ptr
                              | SBSE.Cons_list_sterm (
                                  actual_ptr, l2) ->
                                  (match l2 with
                                     | SBSE.Nil_list_sterm ->
                                         if eq_sterm_upto_cast ptr actual_ptr
                                         then true
                                         else safe_fptr_access_aux sm1 ptr
                                     | SBSE.Cons_list_sterm (
                                         s1, l3) ->
                                         safe_fptr_access_aux sm1 ptr))))
        else safe_fptr_access_aux sm1 ptr

(** val safe_fptr_access : SBSE.smem -> SBSE.sterm -> bool **)

let safe_fptr_access sm ptr = match ptr with
  | SBSE.Coq_sterm_val v ->
      (match v with
         | LLVMsyntax.Coq_value_id i -> safe_fptr_access_aux sm ptr
         | LLVMsyntax.Coq_value_const c ->
             (match c with
                | LLVMsyntax.Coq_const_gid (t, fid2) -> true
                | _ -> safe_fptr_access_aux sm ptr))
  | _ -> safe_fptr_access_aux sm ptr

(** val mtv_iscall :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> SBSE.smem ->
    sicall -> bool **)

let mtv_iscall ps2 fid l1 i1 sm = function
  | Coq_stmn_icall_nptr (i, n, c, t, t2, tsts2) ->
      if match remove_cast t2 with
           | SBSE.Coq_sterm_val v ->
               (match v with
                  | LLVMsyntax.Coq_value_id i0 -> true
                  | LLVMsyntax.Coq_value_const c0 ->
                      (match c0 with
                         | LLVMsyntax.Coq_const_gid (
                             t0, fid2) ->
                             if SBSE.isCallLib fid2
                             then true
                             else (match SBsyntax.lookupFdefViaIDFromProducts
                                           ps2 fid2 with
                                     | Some f ->
                                         let SBsyntax.Coq_fdef_intro
                                           (f0, b) = f
                                         in
                                         let LLVMsyntax.Coq_fheader_intro
                                           (f1, t1, i0, args2, v0) = f0
                                         in
                                         mtv_func_metadata 
                                           (get_metadata ()) ps2 fid l1 i1
                                           fid2 args2 tsts2
                                     | None -> true)
                         | _ -> true))
           | _ -> true
      then safe_fptr_access sm t2
      else false
  | Coq_stmn_icall_ptr
      (i, n, c, t, t2, tsts2, i0, i2, i3, i4, i5, i6, i7, c0, c1, c3) ->
      if match remove_cast t2 with
           | SBSE.Coq_sterm_val v ->
               (match v with
                  | LLVMsyntax.Coq_value_id i8 -> true
                  | LLVMsyntax.Coq_value_const c4 ->
                      (match c4 with
                         | LLVMsyntax.Coq_const_gid (
                             t0, fid2) ->
                             if SBSE.isCallLib fid2
                             then true
                             else (match SBsyntax.lookupFdefViaIDFromProducts
                                           ps2 fid2 with
                                     | Some f ->
                                         let SBsyntax.Coq_fdef_intro
                                           (f0, b) = f
                                         in
                                         let LLVMsyntax.Coq_fheader_intro
                                           (f1, t1, i8, a, v0) = f0
                                         in
                                         (match a with
                                            | [] -> true
                                            | p::args2 ->
                                                mtv_func_metadata
                                                  (get_metadata ()) ps2 fid
                                                  l1 i1 fid2 args2 tsts2)
                                     | None -> true)
                         | _ -> true))
           | _ -> true
      then safe_fptr_access sm t2
      else false

(** val mtv_subblock :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBsyntax.subblock -> bool **)

let mtv_subblock ps1 ps2 fid l0 nth sb2 =
  let { SBsyntax.coq_NBs = nbs2; SBsyntax.call_cmd = call2 } = sb2 in
  let st2 = SBSE.se_cmds SBSE.sstate_init nbs2 in
  let cl2 = se_icall st2 call2 in
  if if if smem_is_memsafe ps1 ps2 fid l0 nth st2.SBSE.coq_SMem
        then check_all_metadata ps2 fid l0 nth st2.SBSE.coq_STerms
        else false
     then check_addrof_be fid st2.SBSE.coq_STerms
     else false
  then mtv_iscall ps2 fid l0 nth st2.SBSE.coq_SMem cl2
  else false

(** val mtv_subblocks_aux :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> nat -> SBsyntax.subblock list -> bool **)

let rec mtv_subblocks_aux ps1 ps2 fid l0 len = function
  | [] -> true
  | sb2::sbs2' ->
      if mtv_subblock ps1 ps2 fid l0 (minus len (length sbs2')) sb2
      then mtv_subblocks_aux ps1 ps2 fid l0 len sbs2'
      else false

(** val mtv_subblocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l
    -> SBsyntax.subblock list -> bool **)

let mtv_subblocks ps1 ps2 fid l0 sbs2 =
  mtv_subblocks_aux ps1 ps2 fid l0 (length sbs2) (rev sbs2)

(** val mtv_bep_value :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> LLVMsyntax.value ->
    LLVMsyntax.value -> LLVMsyntax.value -> bool -> bool **)

let mtv_bep_value ps2 fid l1 bv ev pv im =
  let p = bv,ev in
  let v,v0 = p in
  (match v with
     | LLVMsyntax.Coq_value_id bid ->
         (match v0 with
            | LLVMsyntax.Coq_value_id eid ->
                (match pv with
                   | LLVMsyntax.Coq_value_id pid ->
                       is_metadata fid l1 O bid eid pid im
                   | LLVMsyntax.Coq_value_const c -> false)
            | LLVMsyntax.Coq_value_const c -> false)
     | LLVMsyntax.Coq_value_const c1 ->
         (match c1 with
            | LLVMsyntax.Coq_const_undef t ->
                (match v0 with
                   | LLVMsyntax.Coq_value_id i -> false
                   | LLVMsyntax.Coq_value_const c ->
                       (match c with
                          | LLVMsyntax.Coq_const_undef t0 ->
                              (match pv with
                                 | LLVMsyntax.Coq_value_id i -> false
                                 | LLVMsyntax.Coq_value_const c0 ->
                                     (match c0 with
                                        | LLVMsyntax.Coq_const_undef t1 ->
                                            true
                                        | _ -> false))
                          | _ -> false))
            | LLVMsyntax.Coq_const_null t0 ->
                (match v0 with
                   | LLVMsyntax.Coq_value_id i -> false
                   | LLVMsyntax.Coq_value_const c ->
                       (match c with
                          | LLVMsyntax.Coq_const_null t ->
                              (match pv with
                                 | LLVMsyntax.Coq_value_id i -> false
                                 | LLVMsyntax.Coq_value_const c0 ->
                                     (match c0 with
                                        | LLVMsyntax.Coq_const_null t1 ->
                                            true
                                        | LLVMsyntax.Coq_const_castop
                                            (c2, c3, t1) ->
                                            (match c2 with
                                               | LLVMsyntax.Coq_castop_inttoptr ->
                                                  true
                                               | _ -> false)
                                        | _ -> false))
                          | LLVMsyntax.Coq_const_castop (
                              c0, c2, t1) ->
                              (match c0 with
                                 | LLVMsyntax.Coq_castop_inttoptr ->
                                     (match c2 with
                                        | LLVMsyntax.Coq_const_int (
                                            s, i0) ->
                                            (match pv with
                                               | LLVMsyntax.Coq_value_id i ->
                                                  false
                                               | LLVMsyntax.Coq_value_const
                                                  c3 ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t, id0) ->
                                                  (match t with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t2 ->
                                                  (match t2 with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t3 ->
                                                  if 
                                                  if 
                                                  if tv_typ t0 t1
                                                  then 
                                                  tv_typ t0
                                                  (LLVMsyntax.Coq_typ_pointer
                                                  (LLVMsyntax.Coq_typ_int
                                                  LLVMsyntax.Size.coq_Eight))
                                                  else false
                                                  then 
                                                  eq_INT_Z i0
                                                  (two_p (Zpos (Coq_xO
                                                  (Coq_xO (Coq_xO (Coq_xO
                                                  (Coq_xI Coq_xH)))))))
                                                  else false
                                                  then 
                                                  (match 
                                                  SBsyntax.lookupGvarFromProducts
                                                  ps2 id0 with
                                                    | 
                                                  Some g ->
                                                  (match g with
                                                    | 
                                                  LLVMsyntax.Coq_gvar_intro
                                                  (i, l0, g0, t4, c4, a) ->
                                                  false
                                                    | 
                                                  LLVMsyntax.Coq_gvar_external
                                                  (i, g0, t4) -> true)
                                                    | 
                                                  None -> false)
                                                  else false
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  _ -> false)
                                                    | 
                                                  _ -> false))
                                        | _ -> false)
                                 | _ -> false)
                          | _ -> false))
            | LLVMsyntax.Coq_const_gid (t, id1) ->
                (match v0 with
                   | LLVMsyntax.Coq_value_id i -> false
                   | LLVMsyntax.Coq_value_const c ->
                       (match c with
                          | LLVMsyntax.Coq_const_gid (
                              t0, id2) ->
                              (match pv with
                                 | LLVMsyntax.Coq_value_id i -> false
                                 | LLVMsyntax.Coq_value_const c0 ->
                                     (match c0 with
                                        | LLVMsyntax.Coq_const_gid
                                            (t1, id3) ->
                                            (match 
                                             SBsyntax.lookupFdecFromProducts
                                               ps2 id1 with
                                               | Some f ->
                                                  if eq_id id1 id2
                                                  then eq_id id2 id3
                                                  else false
                                               | None -> false)
                                        | _ -> false))
                          | LLVMsyntax.Coq_const_gep (
                              i, c2, l0) ->
                              (match c2 with
                                 | LLVMsyntax.Coq_const_gid (
                                     t0, i0) ->
                                     (match l0 with
                                        | LLVMsyntax.Nil_list_const -> false
                                        | LLVMsyntax.Cons_list_const
                                            (c0, l2) ->
                                            (match c0 with
                                               | LLVMsyntax.Coq_const_int
                                                  (s, i2) ->
                                                  (match l2 with
                                                    | 
                                                  LLVMsyntax.Nil_list_const ->
                                                  (match pv with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> false
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c3 ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_const_gid
                                                  (t1, i1) ->
                                                  if 
                                                  if eq_const c1 c2
                                                  then eq_const c1 c3
                                                  else false
                                                  then 
                                                  eq_INT_Z i2 (Zpos Coq_xH)
                                                  else false
                                                    | 
                                                  _ -> false))
                                                    | 
                                                  LLVMsyntax.Cons_list_const
                                                  (c3, l3) -> false)
                                               | _ -> false))
                                 | _ -> false)
                          | _ -> false))
            | _ -> false))

(** val mtv_list_value_l :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.list_value_l ->
    LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool -> bool **)

let rec mtv_list_value_l ps2 fid bvls evls pvls im =
  match bvls with
    | LLVMsyntax.Nil_list_value_l -> true
    | LLVMsyntax.Cons_list_value_l (bv, bl, bvls') ->
        if let o = LLVMinfra.getValueViaLabelFromValuels evls bl in
           let o0 = LLVMinfra.getValueViaLabelFromValuels pvls bl in
           (match o with
              | Some ev ->
                  (match o0 with
                     | Some pv -> mtv_bep_value ps2 fid bl bv ev pv im
                     | None -> false)
              | None -> false)
        then mtv_list_value_l ps2 fid bvls' evls pvls im
        else false

(** val mtv_phinodes_aux :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat -> metadata ->
    LLVMsyntax.phinodes -> bool **)

let rec mtv_phinodes_aux ps2 fid l1 i1 ms ps3 =
  match ms with
    | [] -> true
    | p0::ms' ->
        let p1,im = p0 in
        let p2,p = p1 in
        let p3,e = p2 in
        let p4,b = p3 in
        let p5,i2 = p4 in
        let fid',l2 = p5 in
        if if if if eq_id fid fid' then eq_l l1 l2 else false
              then beq_nat i1 i2
              else false
           then let p6 = (lookupPhinode ps3 b),(lookupPhinode ps3 e) in
                let o = lookupPhinode ps3 p in
                let o0,o1 = p6 in
                (match o0 with
                   | Some p7 ->
                       let LLVMsyntax.Coq_insn_phi (i, t, bvls) = p7 in
                       (match o1 with
                          | Some p8 ->
                              let LLVMsyntax.Coq_insn_phi (i0, t0, evls) = p8
                              in
                              (match o with
                                 | Some p9 ->
                                     let LLVMsyntax.Coq_insn_phi
                                       (i3, t1, pvls) = p9
                                     in
                                     mtv_list_value_l ps2 fid bvls evls pvls
                                       im
                                 | None -> false)
                          | None -> false)
                   | None ->
                       (match o1 with
                          | Some p7 -> false
                          | None ->
                              (match o with
                                 | Some p7 -> false
                                 | None -> true)))
           else true
        then mtv_phinodes_aux ps2 fid l1 i1 ms' ps3
        else false

(** val mtv_phinodes :
    SBsyntax.products -> LLVMsyntax.id -> LLVMsyntax.l -> nat ->
    LLVMsyntax.phinodes -> bool **)

let mtv_phinodes ps2 fid l0 i ps3 =
  mtv_phinodes_aux ps2 fid l0 i (get_metadata ()) ps3

(** val mtv_block :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBsyntax.block -> bool **)

let mtv_block ps1 ps2 fid = function
  | SBsyntax.Coq_block_common (l2, ps3, sbs2, nbs2, tmn2) ->
      if if mtv_phinodes ps2 fid l2 (S (length sbs2)) ps3
         then mtv_subblocks ps1 ps2 fid l2 sbs2
         else false
      then mtv_cmds ps1 ps2 fid l2 nbs2
      else false
  | SBsyntax.Coq_block_ret_ptr (l2, ps3, sbs2, nbs2, i) ->
      let SBsyntax.Coq_insn_return_ptr
        (i0, t, i1, i2, i3, vb, i4, i5, ve, i6, vp, i7, c, c0, c1) = i
      in
      if if if mtv_phinodes ps2 fid l2 (S (length sbs2)) ps3
            then mtv_subblocks ps1 ps2 fid l2 sbs2
            else false
         then mtv_cmds ps1 ps2 fid l2 nbs2
         else false
      then if mtv_bep_value ps2 fid l2 vb ve vp true
           then true
           else mtv_bep_value ps2 fid l2 vb ve vp false
      else false

(** val mtv_blocks :
    LLVMsyntax.products -> SBsyntax.products -> LLVMsyntax.id ->
    SBsyntax.blocks -> bool **)

let rec mtv_blocks ps1 ps2 fid = function
  | [] -> true
  | b2::bs2' ->
      if mtv_block ps1 ps2 fid b2 then mtv_blocks ps1 ps2 fid bs2' else false

(** val mtv_fdef :
    LLVMsyntax.products -> SBsyntax.products -> SBsyntax.fdef -> bool **)

let mtv_fdef ps1 ps2 = function
  | SBsyntax.Coq_fdef_intro (fh2, lb2) ->
      let LLVMsyntax.Coq_fheader_intro (f, t2, fid2, a2, v) = fh2 in
      if SBSE.isCallLib fid2 then true else mtv_blocks ps1 ps2 fid2 lb2

(** val mtv_products :
    LLVMsyntax.products -> SBsyntax.products -> SBsyntax.products -> bool **)

let rec mtv_products ps1 ps20 = function
  | [] -> true
  | p::ps2' ->
      (match p with
         | SBsyntax.Coq_product_fdef f2 ->
             if mtv_fdef ps1 ps20 f2
             then mtv_products ps1 ps20 ps2'
             else false
         | _ -> mtv_products ps1 ps20 ps2')

(** val mtv_module : LLVMsyntax.coq_module -> SBsyntax.coq_module -> bool **)

let mtv_module m1 m2 =
  let LLVMsyntax.Coq_module_intro (l0, n, ps1) = m1 in
  let SBsyntax.Coq_module_intro (l1, n0, ps2) = m2 in
  mtv_products ps1 ps2 ps2

