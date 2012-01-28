Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import syntax.
Require Import infrastructure.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import sb_def.

Module SB_ds_pass.

Import LLVMsyntax.
Import LLVMinfra.
Import LLVMgv.
Export SBspecAux.

(********************************************)
(** syntax *)
Definition i32 := typ_int Size.ThirtyTwo.
Definition i1 := typ_int Size.One.
Definition pp8 := typ_pointer p8.
Definition p32 := typ_pointer i32.
Definition int1 := const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 1%Z false).
Definition vint1 := value_const int1.
Definition c1 := Cons_list_sz_value Size.ThirtyTwo vint1 Nil_list_sz_value.
Definition vnullp8 := value_const (const_null p8).
Definition vnullp32 := value_const (const_null p32).
Definition int0 := const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 0%Z false).
Definition vint0 := value_const int0.

Parameter assert_fid : id.
Parameter fake_id : id.
Parameter gmb_fid : id.
Parameter gme_fid : id.
Parameter smmd_fid : id.
Parameter ssb_fid : id.
Parameter sse_fid : id.
Parameter gsb_fid : id.
Parameter gse_fid : id.
Parameter astk_fid : id.
Parameter dstk_fid : id.

Definition assert_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ))))) false.

Definition assert_fn : value :=
  value_const (const_gid assert_typ assert_fid).

Definition gmb_typ : typ :=
  typ_function p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ p32 Nil_list_typ)))) false.

Definition gmb_fn : value :=
  value_const (const_gid gmb_typ gmb_fid).

Definition gme_typ : typ :=
  typ_function p8
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ p32 Nil_list_typ)))) false.

Definition gme_fn : value :=
  value_const (const_gid gme_typ gme_fid).

Definition smmd_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ)))))) false.

Definition smmd_fn : value :=
  value_const (const_gid smmd_typ smmd_fid).

Definition ssb_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ i32 Nil_list_typ)) false.

Definition ssb_fn : value :=
  value_const (const_gid ssb_typ ssb_fid).

Definition sse_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ i32 Nil_list_typ)) false.

Definition sse_fn : value :=
  value_const (const_gid sse_typ sse_fid).

Definition gsb_typ : typ :=
  typ_function p8 (Cons_list_typ i32 Nil_list_typ) false.

Definition gsb_fn : value :=
  value_const (const_gid gsb_typ gsb_fid).

Definition gse_typ  : typ :=
 typ_function p8 (Cons_list_typ i32 Nil_list_typ) false.

Definition gse_fn : value :=
  value_const (const_gid gse_typ gse_fid).

Definition astk_typ : typ :=
  typ_function typ_void (Cons_list_typ i32 Nil_list_typ) false.

Definition astk_fn : value :=
  value_const (const_gid astk_typ astk_fid).

Definition dstk_typ : typ :=
  typ_function typ_void Nil_list_typ false.

Definition dstk_fn : value :=
  value_const (const_gid dstk_typ dstk_fid).

Definition attrs := clattrs_intro false callconv_ccc nil nil.

(*******************************)
(* Generate metadata *)

Definition getGEPTyp (nts:namedts) (idxs : list_sz_value) (t : typ) : option typ :=
match idxs with
| Nil_list_sz_value => None
| Cons_list_sz_value _ idx idxs' =>
    do t <- Constant.typ2utyp nts t;
    (* The input t is already an element of a pointer typ *)
    do t' <- getSubTypFromValueIdxs idxs' t;
    ret (typ_pointer t')
end.

Definition getCmdTyp (nts:namedts) (i:cmd) : option typ :=
match i with
| insn_bop _ _ sz _ _ => Some (typ_int sz)
| insn_fbop _ _ ft _ _ => Some (typ_floatpoint ft)
(*
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ *)
| insn_extractvalue _ typ _ idxs => 
    do t <- Constant.typ2utyp nts typ;
    getSubTypFromConstIdxs idxs t
| insn_insertvalue _ typ _ _ _ _ => Some typ
| insn_malloc _ typ _ _ => Some (typ_pointer typ)
| insn_free _ typ _ => Some typ_void
| insn_alloca _ typ _ _ => Some (typ_pointer typ)
| insn_load _ typ _ _ => Some typ
| insn_store _ _ _ _ _ => Some typ_void
| insn_gep _ _ typ _ idxs => getGEPTyp nts idxs typ
| insn_trunc _ _ _ _ typ => Some typ
| insn_ext _ _ _ _ typ2 => Some typ2
| insn_cast _ _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_fcmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_select _ _ typ _ _ => Some typ
| insn_call _ true _ typ _ _ => Some typ_void
| insn_call _ false _ typ _ _ => 
    match typ with
    | typ_function t _ _ => Some t
    | _ => None
    end
end.

Definition rmap := list (id*(id*id)).

Definition getFdefLocs fdef : ids :=
match fdef with
| fdef_intro (fheader_intro _ _ _ la _) bs => getArgsIDs la ++ getBlocksLocs bs 
end.

Definition gen_metadata_id (ex_ids:ids) (rm:rmap) (id0:id) 
  : id * id * ids * rmap :=
let '(exist b _) := AtomImpl.atom_fresh_for_list ex_ids in
let '(exist e _) := AtomImpl.atom_fresh_for_list (b::ex_ids) in
(b, e, b::e::ex_ids, (id0,(b,e))::rm).

Fixpoint gen_metadata_cmds nts (ex_ids:ids) (rm:rmap) (cs:cmds) 
  : option(ids*rmap) :=
match cs with
| nil => Some (ex_ids,rm)
| c::cs' => 
   do t <- getCmdTyp nts c;
   if isPointerTypB t then
     let id0 := getCmdLoc c in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_cmds nts ex_ids' rm' cs'
   else gen_metadata_cmds nts ex_ids rm cs'
end.

Fixpoint gen_metadata_phinodes (ex_ids:ids) (rm:rmap) (ps:phinodes) : ids*rmap :=
match ps with
| nil => (ex_ids,rm)
| p::ps' => 
   let t := getPhiNodeTyp p in
   if isPointerTypB t then
     let id0 := getPhiNodeID p in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_phinodes ex_ids' rm' ps'
   else gen_metadata_phinodes ex_ids rm ps'
end.

Definition gen_metadata_block nts (ex_ids:ids) (rm:rmap) (b:block) 
  : option(ids*rmap) :=
let '(block_intro _ ps cs _) := b in
let '(ex_ids', rm') := gen_metadata_phinodes ex_ids rm ps in
gen_metadata_cmds nts ex_ids' rm' cs.

Fixpoint gen_metadata_blocks nts (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option(ids*rmap) :=
match bs with
| nil => Some (ex_ids,rm)
| b::bs' => 
    match gen_metadata_block nts ex_ids rm b with
    | Some (ex_ids',rm') => gen_metadata_blocks nts ex_ids' rm' bs'
    | None => None
    end
end.

Fixpoint gen_metadata_args (ex_ids:ids) (rm:rmap) (la:args) : ids*rmap :=
match la with
| nil => (ex_ids,rm)
| (t,_,id0)::la' => 
   if isPointerTypB t then
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_args ex_ids' rm' la'
   else gen_metadata_args ex_ids rm la'
end.

Definition gen_metadata_fdef nts (ex_ids:ids) (rm:rmap) (f:fdef) 
  : option(ids*rmap) :=
let '(fdef_intro (fheader_intro _ _ _ la _) bs) := f in
let '(ex_ids', rm') := gen_metadata_args ex_ids rm la in
gen_metadata_blocks nts ex_ids' rm' bs.

(******************************)
(** Translation *)

Axiom isSysLib : id -> bool.

Axiom wrapper_fid : id -> id.

Axiom isCallLib : id -> bool.

Definition mk_tmp (ex_ids:ids) : id * ids :=
let '(exist tmp _) := AtomImpl.atom_fresh_for_list ex_ids in
(tmp, tmp::ex_ids).

Definition type_size t :=
  value_const
    (const_castop 
      castop_ptrtoint 
      (const_gep false 
        (const_null t) 
        (Cons_list_const int1 Nil_list_const))
      (typ_int Size.ThirtyTwo)
    ).

Definition get_reg_metadata (rm:rmap) (v:value) : option (value * value) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some (bid, eid) => Some (value_id bid, value_id eid)
      | None => None
      end
  | value_const c => 
      match (get_const_metadata c) with
      | Some (bc, ec) => Some (value_const bc, value_const ec)
      | None => Some (vnullp8, vnullp8)
      end
  end.

Definition prop_metadata (ex_ids : ids) rm c v1 id0 :=
  match (get_reg_metadata rm v1, lookupAL _ rm id0) with
  | (Some (bv, ev), Some (bid0, eid0)) =>
      Some (ex_ids,
        c::
        insn_cast bid0 castop_bitcast p8 bv p8:: 
        insn_cast eid0 castop_bitcast p8 ev p8:: 
        nil)
  | _ => None
  end.

Definition val32 z := (i32,@nil attribute,
                           (value_const (const_int Size.ThirtyTwo 
                             (INTEGER.of_Z 32%Z z false)))).

Definition call_set_shadowstack bv0 ev0 idx cs : cmds :=
  insn_call fake_id true attrs ssb_typ ssb_fn
      ((p8,nil,bv0)::
       (val32 idx)::
       nil)::
  insn_call fake_id true attrs sse_typ sse_fn
      ((p8,nil,ev0)::
       (val32 idx)::
       nil)::cs.

Fixpoint trans_params (rm:rmap) (lp:params) (idx:Z) : option cmds :=
match lp with
| nil => Some nil
| (t0,_,v0)::lp' =>
    match trans_params rm lp' (idx+1) with
    | Some cs =>
      if isPointerTypB t0 then
        match get_reg_metadata rm v0 with
        | Some (bv0, ev0) => Some (call_set_shadowstack bv0 ev0 idx cs)
        | _ => None
        end
      else Some (call_set_shadowstack vnullp8 vnullp8 idx cs) 
    | _ => None
    end
end.

Definition wrap_call v : value :=
match v with
| value_const (const_gid ft fid) => value_const (const_gid ft (wrapper_fid fid))
| _ => v
end.

Definition isReturnPointerTypB t0 : bool :=
match t0 with
| typ_function t0 _ _ => isPointerTypB t0
| _ => false
end.

Definition call_suffix i0 nr ca t0 v p rm : option cmds :=
  let optcs' :=
    if negb nr && isReturnPointerTypB t0 then
      match (lookupAL _ rm i0) with
      | Some (bid0, eid0) =>
          Some (
            insn_call bid0 false attrs gsb_typ gsb_fn  
              ((i32,nil,vint0)::nil)::
            insn_call eid0 false attrs gse_typ gse_fn 
              ((i32,nil,vint0)::nil)::
            insn_call fake_id true attrs dstk_typ dstk_fn nil::
            nil)
      | None => None
      end
    else 
      Some [insn_call fake_id true attrs dstk_typ dstk_fn nil]
  in
  match optcs' with
  | Some cs' => Some ([insn_call i0 nr ca t0 (wrap_call v) p]++cs')
  | None => None
  end.

Definition trans_cmd (ex_ids:ids) (rm:rmap) (c:cmd) 
  : option (ids*cmds) :=
match c with 
| insn_malloc id0 t1 v1 _ | insn_alloca id0 t1 v1 _ =>
    match lookupAL _ rm id0 with
    | Some (bid, eid) =>
      let '(ntmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      Some (ex_ids,
       insn_cast ntmp castop_bitcast i32 v1 i32:: 
       c::
       insn_gep etmp false t1 (value_id id0) 
         (Cons_list_sz_value Size.ThirtyTwo (value_id ntmp) Nil_list_sz_value) :: 
       insn_cast bid castop_bitcast (typ_pointer t1) (value_id id0) p8:: 
       insn_cast eid castop_bitcast (typ_pointer t1) (value_id etmp) p8:: 
       nil)
    | _ => None
    end

| insn_load id0 t2 v2 align => 
    match get_reg_metadata rm v2 with
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(optcs, ex_ids) := 
        if isPointerTypB t2 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
                   (Some
                     (insn_call bid0 false attrs gmb_typ gmb_fn 
                       ((p8,nil,(value_id ptmp))::
                        (p8,nil,vnullp8)::
                        (i32,nil,vint1)::
                        (p32,nil,vnullp32)::
                        nil)::
                      insn_call eid0 false attrs gme_typ gme_fn 
                       ((p8,nil,(value_id ptmp))::
                        (p8,nil,vnullp8)::
                        (i32,nil,vint1)::
                        (p32,nil,vnullp32)::
                        nil)::
                      nil), ex_ids)
          | None => (None, ex_ids)
          end
        else (Some nil, ex_ids) in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids,
         insn_cast ptmp castop_bitcast (typ_pointer t2) v2 p8:: 
         insn_call fake_id true attrs assert_typ assert_fn 
           ((p8,nil,bv)::
            (p8,nil,ev)::
            (p8,nil,(value_id ptmp))::
            (i32,nil,type_size t2)::
            (i32,nil,vint1)::nil)::
            c :: cs)
      end
    | None => None
    end

| insn_store id0 t0 v1 v2 align =>
    match get_reg_metadata rm v2 with
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t0 then
          match get_reg_metadata rm v1 with
          | Some (bv0, ev0) =>
              Some
                (insn_call fake_id true attrs smmd_typ smmd_fn 
                  ((p8,nil,(value_id ptmp))::
                   (p8,nil,bv0)::
                   (p8,nil,ev0)::
                   (p8,nil,vnullp8)::
                   (i32,nil,vint1)::
                   (i32,nil,vint1)::
                   nil)::
                 nil)
          | None => None
          end
        else Some nil in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids,
         insn_cast ptmp castop_bitcast (typ_pointer t0) v2 p8:: 
         insn_call fake_id true attrs assert_typ assert_fn 
           ((p8,nil,bv)::
            (p8,nil,ev)::
            (p8,nil,(value_id ptmp))::
            (i32,nil,(type_size t0))::
            (i32,nil,vint1)::nil)::
         c::
         cs)
      end
    | None => None
    end

| insn_gep id0 inbounds0 t1 v1 lv2 => 
    prop_metadata ex_ids rm c v1 id0

| insn_cast id0 op0 t1 v1 t2 => 
    match op0 with
    | castop_bitcast =>
        if isPointerTypB t1 then
          prop_metadata ex_ids rm c v1 id0
        else Some (ex_ids, [c])
    | castop_inttoptr =>
        match lookupAL _ rm id0 with
        | Some (bid0, eid0) =>
            Some (ex_ids, 
              c::
              insn_cast bid0 castop_bitcast p8 vnullp8 p8::
              insn_cast eid0 castop_bitcast p8 vnullp8 p8::
              nil)
        | _ => None
        end
    | _ => Some (ex_ids, [c])
    end

| insn_select id0 v0 t0 v1 v2 =>
    if isPointerTypB t0 then
      match (get_reg_metadata rm v1, get_reg_metadata rm v2, 
             lookupAL _ rm id0) with
      | (Some (bv1, ev1), Some (bv2, ev2), Some (bid0, eid0)) =>
          let '(ctmp,ex_ids) := mk_tmp ex_ids in
          Some (ex_ids,
            insn_cast ctmp castop_bitcast i1 v0 i1::
            c::
            insn_select bid0 (value_id ctmp) p8 bv1 bv2:: 
            insn_select eid0 (value_id ctmp) p8 ev1 ev2:: 
            nil)
      | _ => None
      end
    else Some (ex_ids, [c])

| insn_call i0 n ca t0 v p =>
    match trans_params rm p 1%Z, call_suffix i0 n ca t0 v p rm with
    | Some cs, Some cs' =>
        Some (ex_ids, 
              insn_call fake_id true attrs
                astk_typ astk_fn
                (val32 (Z_of_nat (length p+1))::
                nil)::               
              cs++cs')
     | _, _ => None
    end

| _ => Some (ex_ids, [c])
end.

Fixpoint trans_cmds (ex_ids:ids) (rm:rmap) (cs:list cmd) 
  : option (ids*cmds) :=
match cs with
| nil => Some (ex_ids, nil)
| c::cs' =>
    match (trans_cmd ex_ids rm c) with
    | Some (ex_ids1, cs1) =>
        match (trans_cmds ex_ids1 rm cs') with
        | Some (ex_ids2, cs2) => 
            Some (ex_ids2, cs1++cs2)
        | _ => None
        end
    | _ => None
    end
end.

Fixpoint get_metadata_from_list_value_l (rm:rmap) (vls:list_value_l) 
  : option (list_value_l * list_value_l) :=
match vls with
| Nil_list_value_l => Some (Nil_list_value_l, Nil_list_value_l)
| Cons_list_value_l v0 l0 vls' => 
    match (get_reg_metadata rm v0, get_metadata_from_list_value_l rm vls') with
    | (Some (bv, ev), Some (baccum, eaccum)) =>
        Some (Cons_list_value_l bv l0 baccum, Cons_list_value_l ev l0 eaccum)
    | _ => None
    end
end.

Fixpoint trans_phinodes (rm:rmap) (ps:phinodes) : option phinodes :=
match ps with
| nil => Some nil
| (insn_phi id0 t0 vls0 as p)::ps' =>
    match trans_phinodes rm ps' with
    | None => None
    | Some ps2 =>
        if isPointerTypB t0 then
          match (get_metadata_from_list_value_l rm vls0,
                lookupAL _ rm id0) with
          | (Some (bvls0, evls0), Some (bid0, eid0)) => 
              Some (insn_phi eid0 p8 evls0::insn_phi bid0 p8 bvls0::p::ps2)
          | _ => None
          end
        else Some (p::ps2)
    end
end.

Definition trans_terminator (rm:rmap) (tmn1:terminator) : option cmds :=
  match tmn1 with
  | insn_return _ t0 v0 =>
    if isPointerTypB t0 then
      match get_reg_metadata rm v0 with
      | Some (bv, ev) =>
          Some (
           insn_call fake_id true attrs ssb_typ ssb_fn
             ((p8,nil,bv)::(i32,nil,vint0)::nil)::
           insn_call fake_id true attrs sse_typ sse_fn
             ((p8,nil,ev)::(i32,nil,vint0)::nil)::
           nil)
      | None => None
      end
    else 
      Some (
        insn_call fake_id true attrs ssb_typ ssb_fn
          ((p8,nil,vnullp8)::(i32,nil,vint0)::nil)::
        insn_call fake_id true attrs sse_typ sse_fn
          ((p8,nil,vnullp8)::(i32,nil,vint0)::nil)::
        nil)
  | _ => Some nil
  end.

Definition trans_block (ex_ids:ids) (rm:rmap) (b:block) 
  : option (ids*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_cmds ex_ids rm cs1 with
    | Some (ex_ids',cs2) => 
        match trans_terminator rm tmn1 with
        | Some cs' =>
            Some (ex_ids',block_intro l1 ps2 (cs2++cs') tmn1)
        | _ => None
        end
    | None => None
    end
end.

Fixpoint trans_blocks (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option (ids*blocks) :=
match bs with
| nil => Some (ex_ids, nil)
| b::bs' =>
    match (trans_block ex_ids rm b) with
    | Some (ex_ids1, b1) =>
        match (trans_blocks ex_ids1 rm bs') with
        | Some (ex_ids2, bs2) => 
            Some (ex_ids2, b1::bs2)
        | _ => None
        end
    | _ => None
    end
end.

Definition call_get_shadowstack bid0 eid0 idx cs : cmds :=
  insn_call bid0 false attrs
    gsb_typ gsb_fn  
      ((i32,nil,(value_const (const_int Size.ThirtyTwo 
        (INTEGER.of_Z 32%Z idx false))))::nil)::
  insn_call eid0 false attrs
    gse_typ gse_fn 
      ((i32,nil,(value_const (const_int Size.ThirtyTwo 
        (INTEGER.of_Z 32%Z idx false))))::nil)::
  cs.

Fixpoint trans_args (rm:rmap) (la:args) (idx:Z) : option cmds :=
match la with
| nil => Some nil
| (t0,_,id0)::la' =>
    match trans_args rm la' (idx+1) with
    | Some cs =>
      if isPointerTypB t0 then
        match (lookupAL _ rm id0) with
        | Some (bid0, eid0) => Some (call_get_shadowstack bid0 eid0 idx cs)
        | _ => None
        end
      else Some cs
    | _ => None
    end
end.

Definition trans_fdef nts (f:fdef) : option fdef :=
let '(fdef_intro (fheader_intro fa t fid la va) bs) := f in
if isCallLib fid then Some f
else
  let ex_ids := getFdefLocs f in
  match gen_metadata_fdef nts ex_ids nil f with
  | Some (ex_ids,rm) =>
      match (trans_args rm la 1%Z) with
      | Some cs' =>
          match (trans_blocks ex_ids rm bs) with
          | Some (ex_ids, (block_intro l1 ps1 cs1 tmn1)::bs') => 
              Some (fdef_intro 
                     (fheader_intro fa t (wrapper_fid fid) la va) 
                     ((block_intro l1 ps1 (cs'++cs1) tmn1)::bs'))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition trans_fdec (f:fdec) : fdec :=
let '(fdec_intro (fheader_intro fa t fid la va)) := f in
fdec_intro (fheader_intro fa t (wrapper_fid fid) la va). 

Definition trans_product nts (p:product) : option product :=
match p with
| product_fdef f =>
    match trans_fdef nts f with
    | None => None
    | Some f' => Some (product_fdef f')
    end
| product_fdec f => Some (product_fdec (trans_fdec f))
| _ => Some p
end.

Fixpoint trans_products nts (ps:products) : option products :=
match ps with
| nil => Some nil
| p::ps' =>
    match (trans_product nts p) with
    | Some p1 =>
        match (trans_products nts ps') with
        | Some ps2 => Some (p1::ps2)
        | _ => None
        end
    | _ => None
    end
end.

Definition trans_module (m:module) : option module :=
let '(module_intro los nts ps) := m in
do ps' <- trans_products nts ps;
ret (module_intro los nts ps').

Fixpoint trans_system (ms:system) : option system :=
match ms with
| nil => Some nil
| m::ms' =>
    match (trans_module m) with
    | Some m1 =>
        match (trans_system ms') with
        | Some ms2 => Some (m1::ms2)
        | _ => None
        end
    | _ => None
    end
end.

(* Freshness *)

Definition getValueID (v:value) : atoms :=
match v with
| value_id id => {{id}}
| value_const _ => {}
end.

Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => True
end.

Fixpoint ids2atoms (ids0:ids) : atoms :=
match ids0 with
| nil => {}
| id0::ids0' => {{id0}} `union` ids2atoms ids0'
end.

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.

Fixpoint rm_codom_disjoint (rm:rmap) : Prop :=
match rm with
| nil => True
| (id0,(bid,eid))::rm' => 
    id0 <> bid /\ id0 <> eid /\ bid <> eid /\ 
    id0 `notin` codom rm' /\
    bid `notin` dom rm' `union` codom rm' /\
    eid `notin` dom rm' `union` codom rm' /\
    rm_codom_disjoint rm' 
end.

End SB_ds_pass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-impredicative-set") ***
*** End: ***
 *)
