open BinInt
open BinPos
open Datatypes
open Metatheory
open MetatheoryAtom
open Peano
open Alist
open Infrastructure
open Monad
open Sb_def
open Syntax

module SB_ds_pass = 
 struct 
  (** val i32 : LLVMsyntax.typ **)
  
  let i32 =
    LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_ThirtyTwo
  
  (** val i1 : LLVMsyntax.typ **)
  
  let i1 =
    LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One
  
  (** val pp8 : LLVMsyntax.typ **)
  
  let pp8 =
    LLVMsyntax.Coq_typ_pointer SBspecAux.p8
  
  (** val p32 : LLVMsyntax.typ **)
  
  let p32 =
    LLVMsyntax.Coq_typ_pointer i32
  
  (** val int1 : LLVMsyntax.const **)
  
  let int1 =
    LLVMsyntax.Coq_const_int (LLVMsyntax.Size.coq_ThirtyTwo,
      (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))) (Zpos Coq_xH) false))
  
  (** val vint1 : LLVMsyntax.value **)
  
  let vint1 =
    LLVMsyntax.Coq_value_const int1
  
  (** val c1 : LLVMsyntax.list_sz_value **)
  
  let c1 =
    LLVMsyntax.Cons_list_sz_value (LLVMsyntax.Size.coq_ThirtyTwo, vint1,
      LLVMsyntax.Nil_list_sz_value)
  
  (** val vnullp8 : LLVMsyntax.value **)
  
  let vnullp8 =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_null SBspecAux.p8)
  
  (** val vnullp32 : LLVMsyntax.value **)
  
  let vnullp32 =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_null p32)
  
  (** val int0 : LLVMsyntax.const **)
  
  let int0 =
    LLVMsyntax.Coq_const_int (LLVMsyntax.Size.coq_ThirtyTwo,
      (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))) Z0 false))
  
  (** val vint0 : LLVMsyntax.value **)
  
  let vint0 =
    LLVMsyntax.Coq_value_const int0
  
  (** val assert_fid : LLVMsyntax.id **)
  
  let assert_fid = Softbound_aux.assert_mptr_fid
  
  (** val fake_id : LLVMsyntax.id **)
  
  let fake_id = Softbound_aux.fake_id
  
  (** val gmb_fid : LLVMsyntax.id **)
  
  let gmb_fid = Softbound_aux.get_mmetadata_base_fid
  
  (** val gme_fid : LLVMsyntax.id **)
  
  let gme_fid = Softbound_aux.get_mmetadata_bound_fid
  
  (** val smmd_fid : LLVMsyntax.id **)
  
  let smmd_fid = Softbound_aux.set_mmetadata_fid
  
  (** val ssb_fid : LLVMsyntax.id **)
  
  let ssb_fid = Softbound_aux.set_shadowstack_base_fid
  
  (** val sse_fid : LLVMsyntax.id **)
  
  let sse_fid = Softbound_aux.set_shadowstack_bound_fid
  
  (** val gsb_fid : LLVMsyntax.id **)
  
  let gsb_fid = Softbound_aux.get_shadowstack_base_fid
  
  (** val gse_fid : LLVMsyntax.id **)
  
  let gse_fid = Softbound_aux.get_shadowstack_bound_fid
  
  (** val astk_fid : LLVMsyntax.id **)
  
  let astk_fid = Softbound_aux.allocate_shadowstack_fid
  
  (** val dstk_fid : LLVMsyntax.id **)
  
  let dstk_fid = Softbound_aux.free_shadowstack_fid
  
  (** val assert_typ : LLVMsyntax.typ **)
  
  let assert_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      (LLVMsyntax.Cons_list_typ (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (SBspecAux.p8, (LLVMsyntax.Cons_list_typ (SBspecAux.p8,
      (LLVMsyntax.Cons_list_typ (i32, (LLVMsyntax.Cons_list_typ (i32,
      LLVMsyntax.Nil_list_typ)))))))))), false)
  
  (** val assert_fn : LLVMsyntax.value **)
  
  let assert_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (assert_typ,
      assert_fid))
  
  (** val gmb_typ : LLVMsyntax.typ **)
  
  let gmb_typ =
    LLVMsyntax.Coq_typ_function (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (SBspecAux.p8, (LLVMsyntax.Cons_list_typ (SBspecAux.p8,
      (LLVMsyntax.Cons_list_typ (i32, (LLVMsyntax.Cons_list_typ (p32,
      LLVMsyntax.Nil_list_typ)))))))), false)
  
  (** val gmb_fn : LLVMsyntax.value **)
  
  let gmb_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (gmb_typ, gmb_fid))
  
  (** val gme_typ : LLVMsyntax.typ **)
  
  let gme_typ =
    LLVMsyntax.Coq_typ_function (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (SBspecAux.p8, (LLVMsyntax.Cons_list_typ (SBspecAux.p8,
      (LLVMsyntax.Cons_list_typ (i32, (LLVMsyntax.Cons_list_typ (p32,
      LLVMsyntax.Nil_list_typ)))))))), false)
  
  (** val gme_fn : LLVMsyntax.value **)
  
  let gme_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (gme_typ, gme_fid))
  
  (** val smmd_typ : LLVMsyntax.typ **)
  
  let smmd_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      (LLVMsyntax.Cons_list_typ (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (SBspecAux.p8, (LLVMsyntax.Cons_list_typ (SBspecAux.p8,
      (LLVMsyntax.Cons_list_typ (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (i32, (LLVMsyntax.Cons_list_typ (i32,
      LLVMsyntax.Nil_list_typ)))))))))))), false)
  
  (** val smmd_fn : LLVMsyntax.value **)
  
  let smmd_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (smmd_typ,
      smmd_fid))
  
  (** val ssb_typ : LLVMsyntax.typ **)
  
  let ssb_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      (LLVMsyntax.Cons_list_typ (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (i32, LLVMsyntax.Nil_list_typ)))), false)
  
  (** val ssb_fn : LLVMsyntax.value **)
  
  let ssb_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (ssb_typ, ssb_fid))
  
  (** val sse_typ : LLVMsyntax.typ **)
  
  let sse_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      (LLVMsyntax.Cons_list_typ (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (i32, LLVMsyntax.Nil_list_typ)))), false)
  
  (** val sse_fn : LLVMsyntax.value **)
  
  let sse_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (sse_typ, sse_fid))
  
  (** val gsb_typ : LLVMsyntax.typ **)
  
  let gsb_typ =
    LLVMsyntax.Coq_typ_function (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (i32, LLVMsyntax.Nil_list_typ)), false)
  
  (** val gsb_fn : LLVMsyntax.value **)
  
  let gsb_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (gsb_typ, gsb_fid))
  
  (** val gse_typ : LLVMsyntax.typ **)
  
  let gse_typ =
    LLVMsyntax.Coq_typ_function (SBspecAux.p8, (LLVMsyntax.Cons_list_typ
      (i32, LLVMsyntax.Nil_list_typ)), false)
  
  (** val gse_fn : LLVMsyntax.value **)
  
  let gse_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (gse_typ, gse_fid))
  
  (** val astk_typ : LLVMsyntax.typ **)
  
  let astk_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      (LLVMsyntax.Cons_list_typ (i32, LLVMsyntax.Nil_list_typ)), false)
  
  (** val astk_fn : LLVMsyntax.value **)
  
  let astk_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (astk_typ,
      astk_fid))
  
  (** val dstk_typ : LLVMsyntax.typ **)
  
  let dstk_typ =
    LLVMsyntax.Coq_typ_function (LLVMsyntax.Coq_typ_void,
      LLVMsyntax.Nil_list_typ, false)
  
  (** val dstk_fn : LLVMsyntax.value **)
  
  let dstk_fn =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_gid (dstk_typ,
      dstk_fid))
  
  (** val attrs : LLVMsyntax.clattrs **)
  
  let attrs =
    LLVMsyntax.Coq_clattrs_intro (false, LLVMsyntax.Coq_callconv_ccc, [], [])
  
  (** val getGEPTyp :
      LLVMsyntax.namedts -> LLVMsyntax.list_sz_value -> LLVMsyntax.typ ->
      LLVMsyntax.typ option **)
  
  let getGEPTyp nts idxs t0 =
    match idxs with
      | LLVMsyntax.Nil_list_sz_value -> None
      | LLVMsyntax.Cons_list_sz_value (s, idx, idxs') ->
          mbind (fun t1 ->
            mbind (fun t' -> Some (LLVMsyntax.Coq_typ_pointer t'))
              (LLVMinfra.getSubTypFromValueIdxs idxs' t1))
            (LLVMinfra.Constant.typ2utyp nts t0)
  
  (** val getCmdTyp :
      LLVMsyntax.namedts -> LLVMsyntax.cmd -> LLVMsyntax.typ option **)
  
  let getCmdTyp nts = function
    | LLVMsyntax.Coq_insn_bop (i0, b, sz, v, v0) -> Some
        (LLVMsyntax.Coq_typ_int sz)
    | LLVMsyntax.Coq_insn_fbop (i0, f, ft, v, v0) -> Some
        (LLVMsyntax.Coq_typ_floatpoint ft)
    | LLVMsyntax.Coq_insn_extractvalue (i0, typ0, v, idxs) ->
        mbind (fun t0 -> LLVMinfra.getSubTypFromConstIdxs idxs t0)
          (LLVMinfra.Constant.typ2utyp nts typ0)
    | LLVMsyntax.Coq_insn_insertvalue (i0, typ0, v, t0, v0, l) -> Some typ0
    | LLVMsyntax.Coq_insn_malloc (i0, typ0, v, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_free (i0, typ0, v) -> Some LLVMsyntax.Coq_typ_void
    | LLVMsyntax.Coq_insn_alloca (i0, typ0, v, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_load (i0, typ0, v, a) -> Some typ0
    | LLVMsyntax.Coq_insn_store (i0, t0, v, v0, a) -> Some
        LLVMsyntax.Coq_typ_void
    | LLVMsyntax.Coq_insn_gep (i0, i2, typ0, v, idxs) ->
        getGEPTyp nts idxs typ0
    | LLVMsyntax.Coq_insn_trunc (i0, t0, t1, v, typ0) -> Some typ0
    | LLVMsyntax.Coq_insn_ext (i0, e, t0, v, typ2) -> Some typ2
    | LLVMsyntax.Coq_insn_cast (i0, c, t0, v, typ0) -> Some typ0
    | LLVMsyntax.Coq_insn_select (i0, v, typ0, v0, v1) -> Some typ0
    | LLVMsyntax.Coq_insn_call (i0, n, c, typ0, v, p) ->
        if n
        then Some LLVMsyntax.Coq_typ_void
        else (match typ0 with
                | LLVMsyntax.Coq_typ_function (t0, l, v0) -> Some t0
                | _ -> None)
    | _ -> Some (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
  
  type rmap = (LLVMsyntax.id*(LLVMsyntax.id*LLVMsyntax.id)) list
  
  (** val getFdefLocs : LLVMsyntax.fdef -> LLVMsyntax.ids **)
  
  let getFdefLocs = function
    | LLVMsyntax.Coq_fdef_intro (f, bs) ->
        let LLVMsyntax.Coq_fheader_intro (f0, t0, i, la, v) = f in
        app (LLVMinfra.getArgsIDs la) (LLVMinfra.getBlocksLocs bs)
  
  (** val gen_metadata_id :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.id ->
      ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.ids)*rmap **)
  
  let gen_metadata_id ex_ids rm id0 =
    let b = AtomImpl.atom_fresh_for_list ex_ids in
    let e = AtomImpl.atom_fresh_for_list (b::ex_ids) in
    ((b,e),(b::(e::ex_ids))),((id0,(b,e))::rm)
  
  (** val gen_metadata_cmds :
      LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.cmds ->
      (LLVMsyntax.ids*rmap) option **)
  
  let rec gen_metadata_cmds nts ex_ids rm = function
    | [] -> Some (ex_ids,rm)
    | c::cs' ->
        mbind (fun t0 ->
          if LLVMinfra.isPointerTypB t0
          then let id0 = LLVMinfra.getCmdLoc c in
               let p,rm' = gen_metadata_id ex_ids rm id0 in
               let p0,ex_ids' = p in gen_metadata_cmds nts ex_ids' rm' cs'
          else gen_metadata_cmds nts ex_ids rm cs') 
          (getCmdTyp nts c)
  
  (** val gen_metadata_phinodes :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.phinodes -> LLVMsyntax.ids*rmap **)
  
  let rec gen_metadata_phinodes ex_ids rm = function
    | [] -> ex_ids,rm
    | p::ps' ->
        let t0 = LLVMinfra.getPhiNodeTyp p in
        if LLVMinfra.isPointerTypB t0
        then let id0 = LLVMinfra.getPhiNodeID p in
             let p0,rm' = gen_metadata_id ex_ids rm id0 in
             let p1,ex_ids' = p0 in gen_metadata_phinodes ex_ids' rm' ps'
        else gen_metadata_phinodes ex_ids rm ps'
  
  (** val gen_metadata_block :
      LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.block ->
      (LLVMsyntax.ids*rmap) option **)
  
  let gen_metadata_block nts ex_ids rm = function
    | LLVMsyntax.Coq_block_intro (l, ps, cs, t0) ->
        let ex_ids',rm' = gen_metadata_phinodes ex_ids rm ps in
        gen_metadata_cmds nts ex_ids' rm' cs
  
  (** val gen_metadata_blocks :
      LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.blocks ->
      (LLVMsyntax.ids*rmap) option **)
  
  let rec gen_metadata_blocks nts ex_ids rm = function
    | [] -> Some (ex_ids,rm)
    | b::bs' ->
        (match gen_metadata_block nts ex_ids rm b with
           | Some p ->
               let ex_ids',rm' = p in gen_metadata_blocks nts ex_ids' rm' bs'
           | None -> None)
  
  (** val gen_metadata_args :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.args -> LLVMsyntax.ids*rmap **)
  
  let rec gen_metadata_args ex_ids rm = function
    | [] -> ex_ids,rm
    | p::la' ->
        let p0,id0 = p in
        let t0,a = p0 in
        if LLVMinfra.isPointerTypB t0
        then let p1,rm' = gen_metadata_id ex_ids rm id0 in
             let p2,ex_ids' = p1 in gen_metadata_args ex_ids' rm' la'
        else gen_metadata_args ex_ids rm la'
  
  (** val gen_metadata_fdef :
      LLVMsyntax.namedts -> LLVMsyntax.ids -> rmap -> LLVMsyntax.fdef ->
      (LLVMsyntax.ids*rmap) option **)
  
  let gen_metadata_fdef nts ex_ids rm = function
    | LLVMsyntax.Coq_fdef_intro (f0, bs) ->
        let LLVMsyntax.Coq_fheader_intro (f1, t0, i, la, v) = f0 in
        let ex_ids',rm' = gen_metadata_args ex_ids rm la in
        gen_metadata_blocks nts ex_ids' rm' bs
  
  (** val isSysLib : LLVMsyntax.id -> bool **)
  
  let isSysLib = Symexe_aux.isSysLib
  
  (** val wrapper_fid : LLVMsyntax.id -> LLVMsyntax.id **)
  
  let wrapper_fid = Softbound_aux.wrapper_fid
  
  (** val isCallLib : LLVMsyntax.id -> bool **)
  
  let isCallLib = Symexe_aux.isCallLib
  
  (** val mk_tmp : LLVMsyntax.ids -> LLVMsyntax.id*LLVMsyntax.ids **)
  
  let mk_tmp ex_ids =
    let tmp = AtomImpl.atom_fresh_for_list ex_ids in tmp,(tmp::ex_ids)
  
  (** val type_size : LLVMsyntax.typ -> LLVMsyntax.value **)
  
  let type_size t0 =
    LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_castop
      (LLVMsyntax.Coq_castop_ptrtoint, (LLVMsyntax.Coq_const_gep (false,
      (LLVMsyntax.Coq_const_null t0), (LLVMsyntax.Cons_list_const (int1,
      LLVMsyntax.Nil_list_const)))), (LLVMsyntax.Coq_typ_int
      LLVMsyntax.Size.coq_ThirtyTwo)))
  
  (** val get_reg_metadata :
      rmap -> LLVMsyntax.value -> (LLVMsyntax.value*LLVMsyntax.value) option **)
  
  let get_reg_metadata rm = function
    | LLVMsyntax.Coq_value_id pid ->
        (match lookupAL rm pid with
           | Some p ->
               let bid,eid = p in
               Some ((LLVMsyntax.Coq_value_id bid),(LLVMsyntax.Coq_value_id
               eid))
           | None -> None)
    | LLVMsyntax.Coq_value_const c ->
        (match SBspecAux.get_const_metadata c with
           | Some p ->
               let bc,ec = p in
               Some ((LLVMsyntax.Coq_value_const
               bc),(LLVMsyntax.Coq_value_const ec))
           | None -> Some (vnullp8,vnullp8))
  
  (** val prop_metadata :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd -> LLVMsyntax.value ->
      AtomImpl.atom -> (LLVMsyntax.ids*LLVMsyntax.cmd list) option **)
  
  let prop_metadata ex_ids rm c v1 id0 =
    let o = get_reg_metadata rm v1 in
    let o0 = lookupAL rm id0 in
    (match o with
       | Some p ->
           let bv,ev = p in
           (match o0 with
              | Some p0 ->
                  let bid0,eid0 = p0 in
                  Some (ex_ids,(c::((LLVMsyntax.Coq_insn_cast (bid0,
                  LLVMsyntax.Coq_castop_bitcast, SBspecAux.p8, bv,
                  SBspecAux.p8))::((LLVMsyntax.Coq_insn_cast (eid0,
                  LLVMsyntax.Coq_castop_bitcast, SBspecAux.p8, ev,
                  SBspecAux.p8))::[]))))
              | None -> None)
       | None -> None)
  
  (** val val32 :
      coq_Z -> (LLVMsyntax.typ*LLVMsyntax.attribute list)*LLVMsyntax.value **)
  
  let val32 z =
    (i32,[]),(LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_int
      (LLVMsyntax.Size.coq_ThirtyTwo,
      (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))) z false))))
  
  (** val call_set_shadowstack :
      LLVMsyntax.value -> LLVMsyntax.value -> coq_Z -> LLVMsyntax.cmd list ->
      LLVMsyntax.cmds **)
  
  let call_set_shadowstack bv0 ev0 idx cs =
    (LLVMsyntax.Coq_insn_call (fake_id, true, attrs, ssb_typ, ssb_fn,
      (((SBspecAux.p8,[]),bv0)::((val32 idx)::[]))))::((LLVMsyntax.Coq_insn_call
      (fake_id, true, attrs, sse_typ, sse_fn,
      (((SBspecAux.p8,[]),ev0)::((val32 idx)::[]))))::cs)
  
  (** val trans_params :
      rmap -> LLVMsyntax.params -> coq_Z -> LLVMsyntax.cmds option **)
  
  let rec trans_params rm lp idx =
    match lp with
      | [] -> Some []
      | p::lp' ->
          let p0,v0 = p in
          let t0,a = p0 in
          (match trans_params rm lp' (coq_Zplus idx (Zpos Coq_xH)) with
             | Some cs ->
                 if LLVMinfra.isPointerTypB t0
                 then (match get_reg_metadata rm v0 with
                         | Some p1 ->
                             let bv0,ev0 = p1 in
                             Some (call_set_shadowstack bv0 ev0 idx cs)
                         | None -> None)
                 else Some (call_set_shadowstack vnullp8 vnullp8 idx cs)
             | None -> None)
  
  (** val wrap_call : LLVMsyntax.value -> LLVMsyntax.value **)
  
  let wrap_call v = match v with
    | LLVMsyntax.Coq_value_id i -> v
    | LLVMsyntax.Coq_value_const c ->
        (match c with
           | LLVMsyntax.Coq_const_gid (ft, fid) -> LLVMsyntax.Coq_value_const
               (LLVMsyntax.Coq_const_gid (ft, (wrapper_fid fid)))
           | _ -> v)
  
  (** val isReturnPointerTypB : LLVMsyntax.typ -> bool **)
  
  let isReturnPointerTypB = function
    | LLVMsyntax.Coq_typ_function (t1, l, v) -> LLVMinfra.isPointerTypB t1
    | _ -> false
  
  (** val call_suffix :
      AtomImpl.atom -> bool -> LLVMsyntax.clattrs -> LLVMsyntax.typ ->
      LLVMsyntax.value -> LLVMsyntax.params -> (LLVMsyntax.id*LLVMsyntax.id)
      coq_AssocList -> LLVMsyntax.cmds option **)
  
  let call_suffix i0 nr ca t0 v p rm =
    let optcs' =
      if if negb nr then isReturnPointerTypB t0 else false
      then (match lookupAL rm i0 with
              | Some y ->
                  let bid0,eid0 = y in
                  Some ((LLVMsyntax.Coq_insn_call (bid0, false, attrs,
                  gsb_typ, gsb_fn,
                  (((i32,[]),vint0)::[])))::((LLVMsyntax.Coq_insn_call (eid0,
                  false, attrs, gse_typ, gse_fn,
                  (((i32,[]),vint0)::[])))::((LLVMsyntax.Coq_insn_call
                  (fake_id, true, attrs, dstk_typ, dstk_fn, []))::[])))
              | None -> None)
      else Some
             (EnvImpl.one (LLVMsyntax.Coq_insn_call (fake_id, true, attrs,
               dstk_typ, dstk_fn, [])))
    in
    (match optcs' with
       | Some cs' -> Some
           (app
             (EnvImpl.one (LLVMsyntax.Coq_insn_call (i0, nr, ca, t0,
               (wrap_call v), p))) cs')
       | None -> None)
  
  (** val trans_cmd :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd ->
      (LLVMsyntax.ids*LLVMsyntax.cmds) option **)
  
  let trans_cmd ex_ids rm c = match c with
    | LLVMsyntax.Coq_insn_malloc (id0, t1, v1, a) ->
        (match lookupAL rm id0 with
           | Some p ->
               let bid,eid = p in
               let ntmp,ex_ids0 = mk_tmp ex_ids in
               let etmp,ex_ids1 = mk_tmp ex_ids0 in
               Some (ex_ids1,((LLVMsyntax.Coq_insn_cast (ntmp,
               LLVMsyntax.Coq_castop_bitcast, i32, v1,
               i32))::(c::((LLVMsyntax.Coq_insn_gep (etmp, false, t1,
               (LLVMsyntax.Coq_value_id id0), (LLVMsyntax.Cons_list_sz_value
               (LLVMsyntax.Size.coq_ThirtyTwo, (LLVMsyntax.Coq_value_id
               ntmp),
               LLVMsyntax.Nil_list_sz_value))))::((LLVMsyntax.Coq_insn_cast
               (bid, LLVMsyntax.Coq_castop_bitcast,
               (LLVMsyntax.Coq_typ_pointer t1), (LLVMsyntax.Coq_value_id
               id0), SBspecAux.p8))::((LLVMsyntax.Coq_insn_cast (eid,
               LLVMsyntax.Coq_castop_bitcast, (LLVMsyntax.Coq_typ_pointer
               t1), (LLVMsyntax.Coq_value_id etmp), SBspecAux.p8))::[]))))))
           | None -> None)
    | LLVMsyntax.Coq_insn_alloca (id0, t1, v1, a) ->
        (match lookupAL rm id0 with
           | Some p ->
               let bid,eid = p in
               let ntmp,ex_ids0 = mk_tmp ex_ids in
               let etmp,ex_ids1 = mk_tmp ex_ids0 in
               Some (ex_ids1,((LLVMsyntax.Coq_insn_cast (ntmp,
               LLVMsyntax.Coq_castop_bitcast, i32, v1,
               i32))::(c::((LLVMsyntax.Coq_insn_gep (etmp, false, t1,
               (LLVMsyntax.Coq_value_id id0), (LLVMsyntax.Cons_list_sz_value
               (LLVMsyntax.Size.coq_ThirtyTwo, (LLVMsyntax.Coq_value_id
               ntmp),
               LLVMsyntax.Nil_list_sz_value))))::((LLVMsyntax.Coq_insn_cast
               (bid, LLVMsyntax.Coq_castop_bitcast,
               (LLVMsyntax.Coq_typ_pointer t1), (LLVMsyntax.Coq_value_id
               id0), SBspecAux.p8))::((LLVMsyntax.Coq_insn_cast (eid,
               LLVMsyntax.Coq_castop_bitcast, (LLVMsyntax.Coq_typ_pointer
               t1), (LLVMsyntax.Coq_value_id etmp), SBspecAux.p8))::[]))))))
           | None -> None)
    | LLVMsyntax.Coq_insn_load (id0, t2, v2, align) ->
        (match get_reg_metadata rm v2 with
           | Some p ->
               let bv,ev = p in
               let ptmp,ex_ids0 = mk_tmp ex_ids in
               if LLVMinfra.isPointerTypB t2
               then (match lookupAL rm id0 with
                       | Some p0 ->
                           let bid0,eid0 = p0 in
                           let optcs = Some ((LLVMsyntax.Coq_insn_call (bid0,
                             false, attrs, gmb_typ, gmb_fn,
                             (((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                             ptmp))::(((SBspecAux.p8,[]),vnullp8)::(((i32,[]),vint1)::(((p32,[]),vnullp32)::[]))))))::((LLVMsyntax.Coq_insn_call
                             (eid0, false, attrs, gme_typ, gme_fn,
                             (((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                             ptmp))::(((SBspecAux.p8,[]),vnullp8)::(((i32,[]),vint1)::(((p32,[]),vnullp32)::[]))))))::[]))
                           in
                           (match optcs with
                              | Some cs -> Some
                                  (ex_ids0,((LLVMsyntax.Coq_insn_cast (ptmp,
                                  LLVMsyntax.Coq_castop_bitcast,
                                  (LLVMsyntax.Coq_typ_pointer t2), v2,
                                  SBspecAux.p8))::((LLVMsyntax.Coq_insn_call
                                  (fake_id, true, attrs, assert_typ,
                                  assert_fn,
                                  (((SBspecAux.p8,[]),bv)::(((SBspecAux.p8,[]),ev)::(((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                                  ptmp))::(((i32,[]),
                                  (type_size t2))::(((i32,[]),vint1)::[])))))))::(c::cs))))
                              | None -> None)
                       | None ->
                           let optcs = None in
                           (match optcs with
                              | Some cs -> Some
                                  (ex_ids0,((LLVMsyntax.Coq_insn_cast (ptmp,
                                  LLVMsyntax.Coq_castop_bitcast,
                                  (LLVMsyntax.Coq_typ_pointer t2), v2,
                                  SBspecAux.p8))::((LLVMsyntax.Coq_insn_call
                                  (fake_id, true, attrs, assert_typ,
                                  assert_fn,
                                  (((SBspecAux.p8,[]),bv)::(((SBspecAux.p8,[]),ev)::(((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                                  ptmp))::(((i32,[]),
                                  (type_size t2))::(((i32,[]),vint1)::[])))))))::(c::cs))))
                              | None -> None))
               else let optcs = Some [] in
                    (match optcs with
                       | Some cs -> Some (ex_ids0,((LLVMsyntax.Coq_insn_cast
                           (ptmp, LLVMsyntax.Coq_castop_bitcast,
                           (LLVMsyntax.Coq_typ_pointer t2), v2,
                           SBspecAux.p8))::((LLVMsyntax.Coq_insn_call
                           (fake_id, true, attrs, assert_typ, assert_fn,
                           (((SBspecAux.p8,[]),bv)::(((SBspecAux.p8,[]),ev)::(((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                           ptmp))::(((i32,[]),(type_size t2))::(((i32,[]),vint1)::[])))))))::(c::cs))))
                       | None -> None)
           | None -> None)
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2, align) ->
        (match get_reg_metadata rm v2 with
           | Some p ->
               let bv,ev = p in
               let ptmp,ex_ids0 = mk_tmp ex_ids in
               let optcs =
                 if LLVMinfra.isPointerTypB t0
                 then (match get_reg_metadata rm v1 with
                         | Some p0 ->
                             let bv0,ev0 = p0 in
                             Some ((LLVMsyntax.Coq_insn_call (fake_id, true,
                             attrs, smmd_typ, smmd_fn,
                             (((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                             ptmp))::(((SBspecAux.p8,[]),bv0)::(((SBspecAux.p8,[]),ev0)::(((SBspecAux.p8,[]),vnullp8)::(((i32,[]),vint1)::(((i32,[]),vint1)::[]))))))))::[])
                         | None -> None)
                 else Some []
               in
               (match optcs with
                  | Some cs -> Some (ex_ids0,((LLVMsyntax.Coq_insn_cast
                      (ptmp, LLVMsyntax.Coq_castop_bitcast,
                      (LLVMsyntax.Coq_typ_pointer t0), v2,
                      SBspecAux.p8))::((LLVMsyntax.Coq_insn_call (fake_id,
                      true, attrs, assert_typ, assert_fn,
                      (((SBspecAux.p8,[]),bv)::(((SBspecAux.p8,[]),ev)::(((SBspecAux.p8,[]),(LLVMsyntax.Coq_value_id
                      ptmp))::(((i32,[]),(type_size t0))::(((i32,[]),vint1)::[])))))))::(c::cs))))
                  | None -> None)
           | None -> None)
    | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t1, v1, lv2) ->
        prop_metadata ex_ids rm c v1 id0
    | LLVMsyntax.Coq_insn_cast (id0, op0, t1, v1, t2) ->
        (match op0 with
           | LLVMsyntax.Coq_castop_inttoptr ->
               (match lookupAL rm id0 with
                  | Some p ->
                      let bid0,eid0 = p in
                      Some (ex_ids,(c::((LLVMsyntax.Coq_insn_cast (bid0,
                      LLVMsyntax.Coq_castop_bitcast, SBspecAux.p8, vnullp8,
                      SBspecAux.p8))::((LLVMsyntax.Coq_insn_cast (eid0,
                      LLVMsyntax.Coq_castop_bitcast, SBspecAux.p8, vnullp8,
                      SBspecAux.p8))::[]))))
                  | None -> None)
           | LLVMsyntax.Coq_castop_bitcast ->
               if LLVMinfra.isPointerTypB t1
               then prop_metadata ex_ids rm c v1 id0
               else Some (ex_ids,(EnvImpl.one c))
           | _ -> Some (ex_ids,(EnvImpl.one c)))
    | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) ->
        if LLVMinfra.isPointerTypB t0
        then let p = (get_reg_metadata rm v1),(get_reg_metadata rm v2) in
             let o = lookupAL rm id0 in
             let o0,o1 = p in
             (match o0 with
                | Some p0 ->
                    let bv1,ev1 = p0 in
                    (match o1 with
                       | Some p1 ->
                           let bv2,ev2 = p1 in
                           (match o with
                              | Some p2 ->
                                  let bid0,eid0 = p2 in
                                  let ctmp,ex_ids0 = mk_tmp ex_ids in
                                  Some (ex_ids0,((LLVMsyntax.Coq_insn_cast
                                  (ctmp, LLVMsyntax.Coq_castop_bitcast, i1,
                                  v0, i1))::(c::((LLVMsyntax.Coq_insn_select
                                  (bid0, (LLVMsyntax.Coq_value_id ctmp),
                                  SBspecAux.p8, bv1,
                                  bv2))::((LLVMsyntax.Coq_insn_select (eid0,
                                  (LLVMsyntax.Coq_value_id ctmp),
                                  SBspecAux.p8, ev1, ev2))::[])))))
                              | None -> None)
                       | None -> None)
                | None -> None)
        else Some (ex_ids,(EnvImpl.one c))
    | LLVMsyntax.Coq_insn_call (i0, n, ca, t0, v, p) ->
        (match trans_params rm p (Zpos Coq_xH) with
           | Some cs ->
               (match call_suffix i0 n ca t0 v p rm with
                  | Some cs' -> Some (ex_ids,((LLVMsyntax.Coq_insn_call
                      (fake_id, true, attrs, astk_typ, astk_fn,
                      ((val32 (coq_Z_of_nat (plus (length p) (S O))))::[])))::
                      (app cs cs')))
                  | None -> None)
           | None -> None)
    | _ -> Some (ex_ids,(EnvImpl.one c))
  
  (** val trans_cmds :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.cmd list ->
      (LLVMsyntax.ids*LLVMsyntax.cmds) option **)
  
  let rec trans_cmds ex_ids rm = function
    | [] -> Some (ex_ids,[])
    | c::cs' ->
        (match trans_cmd ex_ids rm c with
           | Some p ->
               let ex_ids1,cs1 = p in
               (match trans_cmds ex_ids1 rm cs' with
                  | Some p0 ->
                      let ex_ids2,cs2 = p0 in Some (ex_ids2,(app cs1 cs2))
                  | None -> None)
           | None -> None)
  
  (** val get_metadata_from_list_value_l :
      rmap -> LLVMsyntax.list_value_l ->
      (LLVMsyntax.list_value_l*LLVMsyntax.list_value_l) option **)
  
  let rec get_metadata_from_list_value_l rm = function
    | LLVMsyntax.Nil_list_value_l -> Some
        (LLVMsyntax.Nil_list_value_l,LLVMsyntax.Nil_list_value_l)
    | LLVMsyntax.Cons_list_value_l (v0, l0, vls') ->
        let o = get_reg_metadata rm v0 in
        let o0 = get_metadata_from_list_value_l rm vls' in
        (match o with
           | Some p ->
               let bv,ev = p in
               (match o0 with
                  | Some p0 ->
                      let baccum,eaccum = p0 in
                      Some ((LLVMsyntax.Cons_list_value_l (bv, l0,
                      baccum)),(LLVMsyntax.Cons_list_value_l (ev, l0,
                      eaccum)))
                  | None -> None)
           | None -> None)
  
  (** val trans_phinodes :
      rmap -> LLVMsyntax.phinodes -> LLVMsyntax.phinodes option **)
  
  let rec trans_phinodes rm = function
    | [] -> Some []
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, vls0) = p in
        (match trans_phinodes rm ps' with
           | Some ps2 ->
               if LLVMinfra.isPointerTypB t0
               then let o = get_metadata_from_list_value_l rm vls0 in
                    let o0 = lookupAL rm id0 in
                    (match o with
                       | Some p0 ->
                           let bvls0,evls0 = p0 in
                           (match o0 with
                              | Some p1 ->
                                  let bid0,eid0 = p1 in
                                  Some ((LLVMsyntax.Coq_insn_phi (eid0,
                                  SBspecAux.p8,
                                  evls0))::((LLVMsyntax.Coq_insn_phi (bid0,
                                  SBspecAux.p8, bvls0))::(p::ps2)))
                              | None -> None)
                       | None -> None)
               else Some (p::ps2)
           | None -> None)
  
  (** val trans_terminator :
      rmap -> LLVMsyntax.terminator -> LLVMsyntax.cmds option **)
  
  let trans_terminator rm = function
    | LLVMsyntax.Coq_insn_return (i, t0, v0) ->
        if LLVMinfra.isPointerTypB t0
        then (match get_reg_metadata rm v0 with
                | Some p ->
                    let bv,ev = p in
                    Some ((LLVMsyntax.Coq_insn_call (fake_id, true, attrs,
                    ssb_typ, ssb_fn,
                    (((SBspecAux.p8,[]),bv)::(((i32,[]),vint0)::[]))))::((LLVMsyntax.Coq_insn_call
                    (fake_id, true, attrs, sse_typ, sse_fn,
                    (((SBspecAux.p8,[]),ev)::(((i32,[]),vint0)::[]))))::[]))
                | None -> None)
        else Some ((LLVMsyntax.Coq_insn_call (fake_id, true, attrs, ssb_typ,
               ssb_fn,
               (((SBspecAux.p8,[]),vnullp8)::(((i32,[]),vint0)::[]))))::((LLVMsyntax.Coq_insn_call
               (fake_id, true, attrs, sse_typ, sse_fn,
               (((SBspecAux.p8,[]),vnullp8)::(((i32,[]),vint0)::[]))))::[]))
    | _ -> Some []
  
  (** val trans_block :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.block ->
      (LLVMsyntax.ids*LLVMsyntax.block) option **)
  
  let trans_block ex_ids rm = function
    | LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) ->
        (match trans_phinodes rm ps1 with
           | Some ps2 ->
               (match trans_cmds ex_ids rm cs1 with
                  | Some p ->
                      let ex_ids',cs2 = p in
                      (match trans_terminator rm tmn1 with
                         | Some cs' -> Some
                             (ex_ids',(LLVMsyntax.Coq_block_intro (l1, ps2,
                             (app cs2 cs'), tmn1)))
                         | None -> None)
                  | None -> None)
           | None -> None)
  
  (** val trans_blocks :
      LLVMsyntax.ids -> rmap -> LLVMsyntax.blocks ->
      (LLVMsyntax.ids*LLVMsyntax.blocks) option **)
  
  let rec trans_blocks ex_ids rm = function
    | [] -> Some (ex_ids,[])
    | b::bs' ->
        (match trans_block ex_ids rm b with
           | Some p ->
               let ex_ids1,b1 = p in
               (match trans_blocks ex_ids1 rm bs' with
                  | Some p0 ->
                      let ex_ids2,bs2 = p0 in Some (ex_ids2,(b1::bs2))
                  | None -> None)
           | None -> None)
  
  (** val call_get_shadowstack :
      LLVMsyntax.id -> LLVMsyntax.id -> coq_Z -> LLVMsyntax.cmd list ->
      LLVMsyntax.cmds **)
  
  let call_get_shadowstack bid0 eid0 idx cs =
    (LLVMsyntax.Coq_insn_call (bid0, false, attrs, gsb_typ, gsb_fn,
      (((i32,[]),(LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_int
      (LLVMsyntax.Size.coq_ThirtyTwo,
      (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))) idx false)))))::[])))::((LLVMsyntax.Coq_insn_call (eid0,
      false, attrs, gse_typ, gse_fn, (((i32,[]),(LLVMsyntax.Coq_value_const
      (LLVMsyntax.Coq_const_int (LLVMsyntax.Size.coq_ThirtyTwo,
      (LLVMsyntax.INTEGER.of_Z (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
        Coq_xH)))))) idx false)))))::[])))::cs)
  
  (** val trans_args :
      rmap -> LLVMsyntax.args -> coq_Z -> LLVMsyntax.cmds option **)
  
  let rec trans_args rm la idx =
    match la with
      | [] -> Some []
      | p::la' ->
          let p0,id0 = p in
          let t0,a = p0 in
          (match trans_args rm la' (coq_Zplus idx (Zpos Coq_xH)) with
             | Some cs ->
                 if LLVMinfra.isPointerTypB t0
                 then (match lookupAL rm id0 with
                         | Some p1 ->
                             let bid0,eid0 = p1 in
                             Some (call_get_shadowstack bid0 eid0 idx cs)
                         | None -> None)
                 else Some cs
             | None -> None)
  
  (** val trans_fdef :
      LLVMsyntax.namedts -> LLVMsyntax.fdef -> LLVMsyntax.fdef option **)
  
  let trans_fdef nts f = match f with
    | LLVMsyntax.Coq_fdef_intro (f0, bs) ->
        let LLVMsyntax.Coq_fheader_intro (fa, t0, fid, la, va) = f0 in
        if isCallLib fid
        then Some f
        else let ex_ids = getFdefLocs f in
             (match gen_metadata_fdef nts ex_ids [] f with
                | Some p ->
                    let ex_ids0,rm = p in
                    (match trans_args rm la (Zpos Coq_xH) with
                       | Some cs' ->
                           (match trans_blocks ex_ids0 rm bs with
                              | Some p0 ->
                                  let ex_ids1,b = p0 in
                                  (match b with
                                     | [] -> None
                                     | b0::bs' ->
                                         let LLVMsyntax.Coq_block_intro
                                           (l1, ps1, cs1, tmn1) = b0
                                         in
                                         Some (LLVMsyntax.Coq_fdef_intro
                                         ((LLVMsyntax.Coq_fheader_intro (fa,
                                         t0, (wrapper_fid fid), la, va)),
                                         ((LLVMsyntax.Coq_block_intro (l1,
                                         ps1, (app cs' cs1), tmn1))::bs'))))
                              | None -> None)
                       | None -> None)
                | None -> None)
  
  (** val trans_fdec : LLVMsyntax.fdec -> LLVMsyntax.fdec **)
  
  let trans_fdec = function
    | LLVMsyntax.Coq_fheader_intro (fa, t0, fid, la, va) ->
        LLVMsyntax.Coq_fheader_intro (fa, t0, (wrapper_fid fid), la, va)
  
  (** val trans_product :
      LLVMsyntax.namedts -> LLVMsyntax.product -> LLVMsyntax.product option **)
  
  let trans_product nts p = match p with
    | LLVMsyntax.Coq_product_gvar g -> Some p
    | LLVMsyntax.Coq_product_fdec f -> Some (LLVMsyntax.Coq_product_fdec
        (trans_fdec f))
    | LLVMsyntax.Coq_product_fdef f ->
        (match trans_fdef nts f with
           | Some f' -> Some (LLVMsyntax.Coq_product_fdef f')
           | None -> None)
  
  (** val trans_products :
      LLVMsyntax.namedts -> LLVMsyntax.products -> LLVMsyntax.products option **)
  
  let rec trans_products nts = function
    | [] -> Some []
    | p::ps' ->
        (match trans_product nts p with
           | Some p1 ->
               (match trans_products nts ps' with
                  | Some ps2 -> Some (p1::ps2)
                  | None -> None)
           | None -> None)
  
  (** val trans_module :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module option **)
  
  let trans_module = function
    | LLVMsyntax.Coq_module_intro (los, nts, ps) ->
        mbind (fun ps' -> Some (LLVMsyntax.Coq_module_intro (los, nts, ps')))
          (trans_products nts ps)
  
  (** val trans_system : LLVMsyntax.system -> LLVMsyntax.system option **)
  
  let rec trans_system = function
    | [] -> Some []
    | m::ms' ->
        (match trans_module m with
           | Some m1 ->
               (match trans_system ms' with
                  | Some ms2 -> Some (m1::ms2)
                  | None -> None)
           | None -> None)
  
  (** val getValueID : LLVMsyntax.value -> AtomSetImpl.t **)
  
  let getValueID = function
    | LLVMsyntax.Coq_value_id id0 -> AtomSetImpl.singleton id0
    | LLVMsyntax.Coq_value_const c -> AtomSetImpl.empty
  
  (** val ids2atoms : LLVMsyntax.ids -> AtomSetImpl.t **)
  
  let rec ids2atoms = function
    | [] -> AtomSetImpl.empty
    | id0::ids0' ->
        AtomSetImpl.union (AtomSetImpl.singleton id0) (ids2atoms ids0')
  
  (** val codom : rmap -> AtomSetImpl.t **)
  
  let rec codom = function
    | [] -> AtomSetImpl.empty
    | p::rm' ->
        let i,p0 = p in
        let bid,eid = p0 in
        AtomSetImpl.union (AtomSetImpl.singleton bid)
          (AtomSetImpl.union (AtomSetImpl.singleton eid) (codom rm'))
 end

