Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Metatheory.
Require Import sub_symexe.
Require Import symexe_tactic.
Require Import alist.
Require Import sub_tv_dec.
Require Import sub_tv_def.
Require Import sub_tv_infer.
Require Import Coq.Bool.Sumbool.
Require Import monad.

Export SBSE.

(***********************************************)
(* Sub TV (based on renaming.db) *)

(* The axiom assumes the memory behavior of a lib call. It says that the 
 * mem state after the lib is the mem state before the lib. This should
 * be admissible in terms of other axioms.
 *
 * Precisely, we should prove user's memspace and metadata memspace are 
 * disjoint. Lib call does not change user's memspace, but can change
 * metadata space.
 *
*)
Axiom smem_lib_sub : id -> bool.

(*
declare weak void @__hashLoadBaseBound(
  i8* %addr_of_ptr, 
  i8** %addr_of_base, 
  i8** %addr_of_bound, 
  i8* %actual_ptr,    // useless 
  i32 %size_of_type,  // useless
  i32* %ptr_safe      // useless
  )

We assume 
  1) We have already checked that %addr_of_base, %addr_of_bound and %ptr_safe 
     are valid when being passed into @__hashLoadBaseBound. 
  2) __hashLoadBaseBound does not change %base, %bound and %ptr_safe.

So, %base, %bound and %ptr_safe are safe to load w/o memsafety checks.
*)
Fixpoint load_from_metadata (sm:smem) (ptr:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => load_from_metadata sm1 ptr
| smem_lib sm1 fid1 sts1 =>
  if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm_upto_cast ptr addr_of_base || 
          eq_sterm_upto_cast ptr addr_of_bound || 
          eq_sterm_upto_cast ptr ptr_safe) 
      then true 
      else load_from_metadata sm1 ptr
    | _ => load_from_metadata sm1 ptr
    end
  else load_from_metadata sm1 ptr
end.

(* In function f1, i1 is renamed to be (rename_id f1 i1) *)
Axiom rename_id : id -> id -> id.

Definition tv_id fid (id1 id2:id) : bool :=
  eq_id (rename_id fid id1) id2.

Axiom tv_id_injective1 : forall fid id1 id2 id1' id2',
  id1 = id2 -> tv_id fid id1 id1' -> tv_id fid id2 id2' -> id1' = id2'.

Axiom tv_id_injective2 : forall fid id1 id2 id1' id2',
  id1 <> id2 -> tv_id fid id1 id1' -> tv_id fid id2 id2' -> id1' <> id2'.

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom rename_fid : id -> id.

Definition tv_fid (fid1 fid2:id) := 
  eq_id (rename_fid fid1) fid2.

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

Fixpoint tv_const fid (c c':const) : bool :=
match (c, c') with
| (const_zeroinitializer t0, const_zeroinitializer t0') => tv_typ t0 t0'
| (const_int _ _, const_int _ _) 
| (const_floatpoint _ _, const_floatpoint _ _)
| (const_undef _, const_undef _)
| (const_null _, const_null _) => eq_const c c'
| (const_arr t0 cs0, const_arr t0' cs0') => 
    tv_typ t0 t0' && tv_list_const fid cs0 cs0'
| (const_struct cs0, const_struct cs0') => tv_list_const fid cs0 cs0'
| (const_gid _ id0, const_gid _ id0') => 
    tv_fid id0 id0' || tv_id fid id0 id0'
| (const_truncop to0 c0 t0, const_truncop to0' c0' t0') =>
    sumbool2bool _ _ (truncop_dec to0 to0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_extop eo0 c0 t0, const_extop eo0' c0' t0') =>
    sumbool2bool _ _ (extop_dec eo0 eo0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_castop co0 c0 t0, const_castop co0' c0' t0') =>
    sumbool2bool _ _ (castop_dec co0 co0') && tv_const fid c0 c0' &&
    tv_typ t0 t0'
| (const_gep ib0 c0 cs0, const_gep ib0' c0' cs0') =>
    sumbool2bool _ _ (inbounds_dec ib0 ib0') && tv_const fid c0 c0' &&
    tv_list_const fid cs0 cs0' 
| (const_select c0 c1 c2, const_select c0' c1' c2') =>
    tv_const fid c0 c0' && tv_const fid c1 c1' && tv_const fid c2 c2'
| (const_icmp cd0 c0 c1, const_icmp cd0' c0' c1') =>
    sumbool2bool _ _ (cond_dec cd0 cd0') &&
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_fcmp fd0 c0 c1, const_fcmp fd0' c0' c1') =>
    sumbool2bool _ _ (fcond_dec fd0 fd0') &&
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_extractvalue c0 cs0, const_extractvalue c0' cs0') =>
    tv_const fid c0 c0' && tv_list_const fid cs0 cs0'
| (const_insertvalue c0 c1 cs0, const_insertvalue c0' c1' cs0') =>
    tv_const fid c0 c0' && tv_const fid c c1' && tv_list_const fid cs0 cs0'
| (const_bop b0 c0 c1, const_bop b0' c0' c1') =>
    sumbool2bool _ _ (bop_dec b0 b0') && 
    tv_const fid c0 c0' && tv_const fid c1 c1'
| (const_fbop f0 c0 c1, const_fbop f0' c0' c1') =>
    sumbool2bool _ _ (fbop_dec f0 f0') && 
    tv_const fid c0 c0' && tv_const fid c1 c1'
| _ => false
end
with tv_list_const fid (cs cs':list_const) : bool :=
match (cs, cs') with
| (Nil_list_const, Nil_list_const) => true
| (Cons_list_const c0 cs0, Cons_list_const c0' cs0') => 
    tv_const fid c0 c0' && tv_list_const fid cs0 cs0'
| _ => false
end.

Definition tv_value fid v1 v2 : bool :=
match (v1, v2) with
| (value_id id1, value_id id2) => tv_id fid id1 id2
| (value_const c1, value_const c2) => tv_const fid c1 c2
| _ => false
end.

(* e.g. calloc -> softbound_calloc *)
Axiom syscall_returns_pointer : id -> bool.

(* From a name in an output program to its original name in the input program. *)
Axiom rename_fid_inv : id -> option id.

Axiom rename_fid_prop1 : forall fid,
  rename_fid_inv (rename_fid fid) = Some fid.

Axiom rename_fid_prop2 : forall fid1 fid2,
  rename_fid_inv fid1 = Some fid2 ->
  rename_fid fid2 = fid1.

(* Ps1 is from the input program. *)
Definition function_returns_pointer Ps1 fid2 : bool :=
match (rename_fid_inv fid2) with
| Some fid1 =>
    match lookupFdefViaIDFromProducts Ps1 fid1 with      
    | Some (fdef_intro (fheader_intro _ (typ_pointer _ as tp) _ _ _) _) => true
    | _ => false
    end
| None => false
end.

(* Additional stores must be at "shadow_ret" *)
Definition store_to_ret Ps1 Ps2 fid2 (ptr:sterm) : bool :=
if (function_returns_pointer Ps1 fid2) then
   match SBsyntax.lookupFdefViaIDFromProducts Ps2 fid2 with      
   | Some (SBsyntax.fdef_intro (fheader_intro _ _  _ ((_,re)::_) _) _) =>
       match remove_cast ptr with
       | sterm_gep _ _ (sterm_val (value_id id0)) 
          (Cons_list_sz_sterm _ (sterm_val (value_const (const_int _ i0)))
          (Cons_list_sz_sterm _ (sterm_val (value_const (const_int _ i1)))
            Nil_list_sz_sterm)) =>
            eq_id id0 re && eq_INT_Z i0 0%Z &&
            (eq_INT_Z i1 0%Z || eq_INT_Z i1 1%Z || eq_INT_Z i1 2%Z) 
       | _ => false
       end
   | _ => false
   end
else false.

Fixpoint tv_sterm Ps1 Ps2 fid (st st':sterm) : bool :=
match (st, st') with
| (sterm_val v, sterm_val v') => tv_value fid v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
    sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
    sumbool2bool _ _ (fbop_dec b b') && 
    sumbool2bool _ _ (floating_point_dec f f') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
    tv_typ t t' && tv_sterm Ps1 Ps2 fid st1 st1' &&
  sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
    tv_typ t1 t1' && tv_sterm Ps1 Ps2 fid st1 st1' && 
    tv_typ t2 t2' && tv_sterm Ps1 Ps2 fid st2 st2' &&
    sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
    tv_smem Ps1 Ps2 fid sm sm' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_align a a'
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
    sumbool2bool _ _ (bool_dec i i') && tv_typ t t' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_list_sz_sterm Ps1 Ps2 fid sts2 sts2'
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
    sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2'
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
    sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2' 
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
    sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t2 t2' 
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
    sumbool2bool _ _ (cond_dec c c') && tv_typ t t' &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
    sumbool2bool _ _ (fcond_dec c c') &&
    sumbool2bool _ _ (floating_point_dec ft ft') &&
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_sterm Ps1 Ps2 fid st2 st2'
| (sterm_phi t stls, sterm_phi t' stls') =>
    tv_typ t t' && tv_list_sterm_l Ps1 Ps2 fid stls stls'
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
    tv_sterm Ps1 Ps2 fid st1 st1' && tv_typ t t' && 
    tv_sterm Ps1 Ps2 fid st2 st2' && tv_sterm Ps1 Ps2 fid st3 st3'
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
    tv_smem Ps1 Ps2 fid sm sm' && eq_id i i' && 
    tv_list_sterm Ps1 Ps2 fid sts sts'
| _ => false
end
with tv_list_sz_sterm Ps1 Ps2 fid (sts sts':list_sz_sterm) : bool :=
match (sts, sts') with
| (Nil_list_sz_sterm, Nil_list_sz_sterm) => true
| (Cons_list_sz_sterm sz0 st sts0, Cons_list_sz_sterm sz0' st' sts0') =>
    sumbool2bool _ _ (Size.dec sz0 sz0') &&
    tv_sterm Ps1 Ps2 fid st st' && tv_list_sz_sterm Ps1 Ps2 fid sts0 sts0'
| _ => false
end
with tv_list_sterm Ps1 Ps2 fid (sts sts':list_sterm) : bool :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => true
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
    tv_sterm Ps1 Ps2 fid st st' && tv_list_sterm Ps1 Ps2 fid sts0 sts0'
| _ => false
end
with tv_list_sterm_l Ps1 Ps2 fid (stls stls':list_sterm_l) : bool :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => true
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
    tv_sterm Ps1 Ps2 fid st st' && sumbool2bool _ _ (l_dec l l') && 
    tv_list_sterm_l Ps1 Ps2 fid stls0 stls0'
| _ => false
end
with tv_smem Ps1 Ps2 fid (sm1 sm2:smem) : bool :=
match (sm1, sm2) with
| (smem_init, _) => true
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    (* additionl alloca *)
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_alloca sm1 t1 st1 a1) sm2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_load sm1 t1 st1 a1) sm2 &&
         load_from_metadata sm2 st2
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    if (tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st11 st21 &&
        tv_sterm Ps1 Ps2 fid st12 st22 && tv_align a1 a2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_store sm1 t1 st11 st12 a1) sm2 &&
         store_to_ret Ps1 Ps2 (rename_fid fid) st22
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (eq_id fid1 fid2 && tv_list_sterm Ps1 Ps2 fid sts1 sts2)
    then tv_smem Ps1 Ps2 fid sm1 sm2
    else tv_smem Ps1 Ps2 fid (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 lid sts) => smem_lib_sub lid && tv_smem Ps1 Ps2 fid sm1 sm2
| (sm1, smem_alloca sm2 t2 st2 a2) => tv_smem Ps1 Ps2 fid sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => 
  (* We check load_from_metadata to ensure that the behavior of output programs 
   * preserves input's. If we did not check, the additional load may be stuck. 
   *)
    tv_smem Ps1 Ps2 fid sm1 sm2 && load_from_metadata sm2 st2
| (sm1, smem_store sm2 t2 st21 st22 a2) => 
  (* We check that the additional stores must be to shadow_ret. *)
    tv_smem Ps1 Ps2 fid sm1 sm2 && store_to_ret Ps1 Ps2 (rename_fid fid) st22
| _ => false
end.

Fixpoint tv_sframe Ps1 Ps2 fid (sf1 sf2:sframe) : bool :=
match (sf1, sf2) with
| (sframe_init, _) => true
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    (* additionl alloca *)
    if (tv_smem Ps1 Ps2 fid sm1 sm2 && tv_typ t1 t2 && 
        tv_sterm Ps1 Ps2 fid st1 st2 && tv_align a1 a2)
    then tv_sframe Ps1 Ps2 fid sf1 sf2
    else tv_sframe Ps1 Ps2 fid (sframe_alloca sm1 sf1 t1 st1 a1) sf2
| _ => false
end.

Fixpoint tv_smap Ps1 Ps2 fid (sm1 sm2:smap) : bool :=
match sm1 with
| nil => true
| (id1,st1)::sm1' =>
  match lookupAL _ sm2 (rename_id fid id1) with
  | None => false
  | Some st2 => tv_sterm Ps1 Ps2 fid st1 st2 && tv_smap Ps1 Ps2 fid sm1' sm2
  end
end.

Definition sub_sstate Ps1 Ps2 fid s1 s2 := 
  tv_smap Ps1 Ps2 fid s1.(STerms) s2.(STerms) &&
  tv_smem Ps1 Ps2 fid s1.(SMem) s2.(SMem)  &&
  tv_sframe Ps1 Ps2 fid s1.(SFrame) s2.(SFrame) &&
  sumbool2bool _ _ (@sterms_dec s1.(SEffects) s2.(SEffects)).

Definition tv_cmds Ps1 Ps2 fid (nbs1 nbs2 : list nbranch) :=
sub_sstate Ps1 Ps2 fid (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2).

Fixpoint tv_sparams Ps1 Ps2 fid (tsts1 tsts2:list (typ*attributes*sterm)) 
  : bool :=
match (tsts1, tsts2) with
| (nil, _) => true
| ((t1,_,st1)::tsts1', (t2,_,st2)::tsts2') => 
  tv_typ t1 t2 && tv_sterm Ps1 Ps2 fid st1 st2 && 
  tv_sparams Ps1 Ps2 fid tsts1' tsts2'
| _ => false
end.

Inductive scall : Set :=
| stmn_call : id -> noret -> clattrs -> typ -> sterm -> 
    list (typ*attributes*sterm) -> scall
.

Definition se_call : forall (st : sstate)(i:cmd)(iscall:isCall i = true), scall.
Proof.
  intros. unfold isCall in iscall.
  destruct i0; try solve [inversion iscall].
  apply (@stmn_call i0 n c t (value2Sterm st.(STerms) v) 
                      (list_param__list_typ_subst_sterm p st.(STerms))).
Defined.

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. 
 * Do not check if their tailc flags match. Softbound changes the flag for
 * system calls, say atoi from tailcall to non-tailcall.
 *)
Definition tv_scall Ps1 Ps2 fid (c1:scall) (c2:sicall) :=
  let '(stmn_call rid1 nr1 _ ty1 t1 tsts1) := c1 in
  match c2 with
  | stmn_icall_nptr rid2 nr2 _ ty2 t2 tsts2 =>
    tv_id fid rid1 rid2 &&
    (sumbool2bool _ _ (noret_dec nr1 nr2)) &&
    tv_typ ty1 ty2 && tv_sparams Ps1 Ps2 fid tsts1 tsts2 && 
    tv_sterm Ps1 Ps2 fid (remove_cast t1) (remove_cast t2)
  | stmn_icall_ptr _ _ _ ty2 t2 tsts2 _ _ rid2 _ _ _ _ _ _ _ =>
    tv_id fid rid1 rid2 &&
    tv_typ ty1 ty2 && tv_sparams Ps1 Ps2 fid tsts1 tsts2 && 
    match ty1 with
    | typ_pointer _ =>
      match (remove_cast t1, remove_cast t2) with
      | (sterm_val (value_const (const_gid _ fid1)),
         sterm_val (value_const (const_gid _ fid2))) => tv_fid fid1 fid2
      | (st1, st2) => tv_sterm Ps1 Ps2 fid st1 st2
      end
    | _ => false
    end
  end.

Definition tv_subblock Ps1 Ps2 fid (sb1:subblock) (sb2:SBsyntax.subblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, SBsyntax.mkSB nbs2 call2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_icall st2 call2 in
  sub_sstate Ps1 Ps2 fid st1 st2 && tv_scall Ps1 Ps2 fid cl1 cl2 
end.

Fixpoint tv_subblocks Ps1 Ps2 fid (sbs1:list subblock) 
  (sbs2:list SBsyntax.subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
    (tv_subblock Ps1 Ps2 fid sb1 sb2) && (tv_subblocks Ps1 Ps2 fid sbs1' sbs2')
| _ => false
end.

Fixpoint tv_list_value_l fid (vls1 vls2:list_value_l) : bool :=
match (vls1, vls2) with
| (Nil_list_value_l, Nil_list_value_l) => true
| (Cons_list_value_l v1 l1 vls1, Cons_list_value_l v2 l2 vls2) =>
    tv_value fid v1 v2 && eq_l l1 l2 && tv_list_value_l fid vls1 vls2
| _ => false
end.

Definition tv_phinode fid (p1 p2:phinode) : bool :=
match (p1, p2) with
| (insn_phi id1 t1 vls1, insn_phi id2 t2 vls2) =>
    tv_id fid id1 id2  && tv_typ t1 t2 && tv_list_value_l fid vls1 vls2
end.

Fixpoint tv_phinodes fid (ps1 ps2:phinodes) : bool :=
match ps1 with
| nil => true
| (insn_phi i1 _ _)as p1::ps1' =>
  match lookupPhinode ps2 (rename_id fid i1) with
  | None => false
  | Some p2 => tv_phinode fid p1 p2 && tv_phinodes fid ps1' ps2
  end
end.

Definition tv_terminator fid (tmn1 tmn2:terminator) : bool :=
match (tmn1, tmn2) with
| (insn_return id1 t1 v1, insn_return id2 t2 v2) => 
    tv_id fid id1 id2 && tv_typ t1 t2 && tv_value fid v1 v2
| (insn_return_void id1, insn_return_void id2) => tv_id fid id1 id2
| (insn_br id1 v1 l11 l12, insn_br id2 v2 l21 l22) =>
    tv_id fid id1 id2 && tv_value fid v1 v2 && eq_l l11 l21 && eq_l l12 l22
| (insn_br_uncond id1 l1, insn_br_uncond id2 l2) =>
    tv_id fid id1 id2 && eq_l l1 l2
| (insn_unreachable id1, insn_unreachable id2) => tv_id fid id1 id2
| _ => false
end.

Definition tv_block Ps1 Ps2 fid (b1:block) (b2:SBsyntax.block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, SBsyntax.block_common l2 ps2 sbs2 nbs2 tmn2) =>
  match (cmds2sbs cs1) with
  | (sbs1, nbs1) =>
    eq_l l1 l2 && tv_phinodes fid ps1 ps2 && 
    tv_subblocks Ps1 Ps2 fid sbs1 sbs2 &&
    tv_cmds Ps1 Ps2 fid nbs1 nbs2 && 
    tv_terminator fid tmn1 tmn2
  end 
| (block_intro l1 ps1 cs1 tmn1, SBsyntax.block_ret_ptr l2 ps2 sbs2 nbs2
    (SBsyntax.insn_return_ptr _ _ _ _ _ _ _ _ _ _ vp _ _ _ _)) =>
  match (cmds2sbs cs1) with
  | (sbs1, nbs1) =>
    eq_l l1 l2 && tv_phinodes fid ps1 ps2 && 
    tv_subblocks Ps1 Ps2 fid sbs1 sbs2 &&
    tv_cmds Ps1 Ps2 fid nbs1 nbs2 && 
    match tmn1 with
    | insn_return id1 _ v1 => tv_value fid v1 vp
    | _ => false
    end
  end 
end.

Fixpoint tv_blocks Ps1 Ps2 fid (bs1:blocks) (bs2:SBsyntax.blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => 
    tv_block Ps1 Ps2 fid b1 b2 && tv_blocks Ps1 Ps2 fid bs1' bs2'
| _ => false
end.

Definition tv_fheader nts1 (f1 f2:fheader) := 
  let '(fheader_intro fa1 t1 fid1 a1 va1) := f1 in
  let '(fheader_intro fa2 t2 fid2 a2 va2) := f2 in
  tv_fid fid1 fid2 &&
  match t1 with
  | typ_pointer _ =>
      match a2 with
      | (typ_pointer t,_,_)::a2' =>
        match SBsyntax.get_ret_typs nts1 t with
        | Some (t01,t02,t03) =>
            tv_typ t1 t01 && tv_typ t02 t03 && 
            tv_typ t02 (typ_pointer (typ_int Size.Eight)) &&
            if syscall_returns_pointer fid1 then
              (*  System call is only declared, but not defined, LLVM only 
                  gnerates tmp variable names for its arguments started from
                  %0. So we simply check if their types are matched.
               *)
              let ts1 := args2Typs a1 in
              let ts2' := args2Typs a2' in
              (sumbool2bool _ _ (prefix_dec _ typ_dec (unmake_list_typ ts1) 
                (unmake_list_typ ts2')))
            else 
              (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2'))
        | None => false
        end
      | _ => false
      end
  | _ => tv_typ t1 t2 && (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2))
  end.

Definition tv_fdec nts1 (f1 f2:fdec) :=
match (f1, f2) with
| (fdec_intro fh1, fdec_intro fh2) => tv_fheader nts1 fh1 fh2
end.

Definition tv_fdef nts1 Ps1 Ps2 (f1:fdef) (f2:SBsyntax.fdef) :=
match (f1, f2) with
| (fdef_intro (fheader_intro _ _ fid1 _ _ as fh1) lb1, 
   SBsyntax.fdef_intro fh2 lb2) =>
  tv_fheader nts1 fh1 fh2 && tv_blocks Ps1 Ps2 fid1 lb1 lb2
end.

Fixpoint tv_products nts1 (Ps10 Ps1:products) (Ps2:SBsyntax.products) : bool :=
match Ps1 with
| nil => true
| product_gvar gv1::Ps1' =>
  match SBsyntax.lookupGvarViaIDFromProducts Ps2 (getGvarID gv1) with
  | None => false
  | Some gv2 => 
      sumbool2bool _ _ (gvar_dec gv1 gv2) && tv_products nts1 Ps10 Ps1' Ps2 
  end
| product_fdec f1::Ps1' =>
  match SBsyntax.lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1)) with
  | None => false
  | Some f2 => tv_fdec nts1 f1 f2 && tv_products nts1 Ps10 Ps1' Ps2 
  end
| product_fdef f1::Ps1' =>
  match SBsyntax.lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1)) with
  | None => false
  | Some f2 => tv_fdef nts1 Ps10 Ps2 f1 f2 && tv_products nts1 Ps10 Ps1' Ps2 
  end
end.

Definition tv_module (m1:module) (m2:SBsyntax.module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, SBsyntax.module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  tv_products nts1 Ps1 Ps1 Ps2
end.

Fixpoint tv_system (S1:system) (S2:SBsyntax.system) :=
match (S1, S2) with
| (nil, nil) => true
| (m1::S1', m2::S2') => tv_module m1 m2 && tv_system S1' S2'
| _ => false
end.

(***********************************************)
(* Sub TV (guessing renamings) *)

Fixpoint rtv_const (c c':const) : bool :=
match (c, c') with
| (const_zeroinitializer t0, const_zeroinitializer t0') => tv_typ t0 t0'
| (const_int _ _, const_int _ _) 
| (const_floatpoint _ _, const_floatpoint _ _)
| (const_undef _, const_undef _)
| (const_null _, const_null _) => eq_const c c'
| (const_arr t0 cs0, const_arr t0' cs0') => 
    tv_typ t0 t0' && rtv_list_const cs0 cs0'
| (const_struct cs0, const_struct cs0') => rtv_list_const cs0 cs0'
| (const_gid _ id0, const_gid _ id0') => 
    tv_fid id0 id0' || 
    eq_id id0 id0' (* assuming global variables are not renamed *)
| (const_truncop to0 c0 t0, const_truncop to0' c0' t0') =>
    sumbool2bool _ _ (truncop_dec to0 to0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_extop eo0 c0 t0, const_extop eo0' c0' t0') =>
    sumbool2bool _ _ (extop_dec eo0 eo0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_castop co0 c0 t0, const_castop co0' c0' t0') =>
    sumbool2bool _ _ (castop_dec co0 co0') && rtv_const c0 c0' &&
    tv_typ t0 t0'
| (const_gep ib0 c0 cs0, const_gep ib0' c0' cs0') =>
    sumbool2bool _ _ (inbounds_dec ib0 ib0') && rtv_const c0 c0' &&
    rtv_list_const cs0 cs0' 
| (const_select c0 c1 c2, const_select c0' c1' c2') =>
    rtv_const c0 c0' && rtv_const c1 c1' && rtv_const c2 c2'
| (const_icmp cd0 c0 c1, const_icmp cd0' c0' c1') =>
    sumbool2bool _ _ (cond_dec cd0 cd0') &&
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_fcmp fd0 c0 c1, const_fcmp fd0' c0' c1') =>
    sumbool2bool _ _ (fcond_dec fd0 fd0') &&
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_extractvalue c0 cs0, const_extractvalue c0' cs0') =>
    rtv_const c0 c0' && rtv_list_const cs0 cs0'
| (const_insertvalue c0 c1 cs0, const_insertvalue c0' c1' cs0') =>
    rtv_const c0 c0' && rtv_const c c1' && rtv_list_const cs0 cs0'
| (const_bop b0 c0 c1, const_bop b0' c0' c1') =>
    sumbool2bool _ _ (bop_dec b0 b0') && 
    rtv_const c0 c0' && rtv_const c1 c1'
| (const_fbop f0 c0 c1, const_fbop f0' c0' c1') =>
    sumbool2bool _ _ (fbop_dec f0 f0') && 
    rtv_const c0 c0' && rtv_const c1 c1'
| _ => false
end
with rtv_list_const (cs cs':list_const) : bool :=
match (cs, cs') with
| (Nil_list_const, Nil_list_const) => true
| (Cons_list_const c0 cs0, Cons_list_const c0' cs0') => 
    rtv_const c0 c0' && rtv_list_const cs0 cs0'
| _ => false
end.

(* mapping from an input local variable to its output local variable within
   a function. *)
Definition renaming := list (id * id).

(* Check if an id is a name of tmp var, e.g. %100 *)
Axiom is_tmp_var : id -> bool.

Definition lookup_renaming r i :=
if is_tmp_var i then
  match lookupAL _ r i with
  | Some i' => Some i'
  | None => None
  end
else Some i.

Definition rtv_id (r:renaming) id1 id2 :=
  match lookup_renaming r id1 with
  | None => eq_id id1 id2
  | Some id2' => eq_id id2 id2'
  end.

Definition rtv_value r v1 v2 : option renaming :=
match (v1, v2) with
| (value_id id1, value_id id2) => 
  match lookup_renaming r id1 with
  | None => Some ((id1,id2)::r)
  | Some id2' => if eq_id id2 id2' then Some r else None
  end
| (value_const c1, value_const c2) => if rtv_const c1 c2 then Some r else None
| _ => None
end.

Fixpoint rtv_sterm Ps1 Ps2 fid r (st st':sterm) : option renaming :=
match (st, st') with
| (sterm_val v, sterm_val v') => rtv_value r v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
    if sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
    if sumbool2bool _ _ (fbop_dec b b') && 
       sumbool2bool _ _ (floating_point_dec f f')
    then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
    if tv_typ t t' && sumbool2bool _ _ (list_const_dec cs cs') then
      rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
    if tv_typ t1 t1' && tv_typ t2 t2' && 
       sumbool2bool _ _ (list_const_dec cs cs') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
    if tv_typ t t' && tv_align a a' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st1 st1')
    else None
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
    if sumbool2bool _ _ (bool_dec i i') && tv_typ t t' then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_list_sz_sterm Ps1 Ps2 fid r sts2 sts2')
    else None
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
    if sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' && tv_typ t2 t2'
    then rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
    if sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' && tv_typ t2 t2' 
    then rtv_sterm Ps1 Ps2 fid r st1 st1'
    else None
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
    if sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' && tv_typ t2 t2' 
    then rtv_sterm Ps1 Ps2 fid r st1 st1' 
    else None
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
    if sumbool2bool _ _ (cond_dec c c') && tv_typ t t' then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
    if sumbool2bool _ _ (fcond_dec c c') &&
       sumbool2bool _ _ (floating_point_dec ft ft') then
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2')
    else None
| (sterm_phi t stls, sterm_phi t' stls') =>
    if tv_typ t t' then rtv_list_sterm_l Ps1 Ps2 fid r stls stls' else None
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
    if tv_typ t t' then 
      rtv_sterm Ps1 Ps2 fid r st1 st1' >>= 
      (fun r => rtv_sterm Ps1 Ps2 fid r st2 st2') >>=
      (fun r => rtv_sterm Ps1 Ps2 fid r st3 st3')
    else None
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
    if eq_id i i' then
      rtv_smem Ps1 Ps2 fid r sm sm' >>=
      (fun r => rtv_list_sterm Ps1 Ps2 fid r sts sts')
    else None
| _ => None
end
with rtv_list_sz_sterm Ps1 Ps2 fid r (sts sts':list_sz_sterm) 
  : option renaming :=
match (sts, sts') with
| (Nil_list_sz_sterm, Nil_list_sz_sterm) => Some r
| (Cons_list_sz_sterm sz0 st sts0, Cons_list_sz_sterm sz0' st' sts0') =>
    if sumbool2bool _ _ (Size.dec sz0 sz0') then
      rtv_sterm Ps1 Ps2 fid r st st' >>=
      fun r => rtv_list_sz_sterm Ps1 Ps2 fid r sts0 sts0'
    else None
| _ => None
end
with rtv_list_sterm Ps1 Ps2 fid r (sts sts':list_sterm) : option renaming :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => Some r
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
    rtv_sterm Ps1 Ps2 fid r st st' >>=
    fun r => rtv_list_sterm Ps1 Ps2 fid r sts0 sts0'
| _ => None
end
with rtv_list_sterm_l Ps1 Ps2 fid r (stls stls':list_sterm_l) 
  : option renaming :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => Some r
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
    if sumbool2bool _ _ (l_dec l l') then
      rtv_sterm Ps1 Ps2 fid r st st' >>=
      fun r => rtv_list_sterm_l Ps1 Ps2 fid r stls0 stls0'
    else None
| _ => None
end
with rtv_smem Ps1 Ps2 fid r (sm1 sm2:smem) : option renaming :=
match (sm1, sm2) with
| (smem_init, _) => Some r
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    if tv_typ t1 t2 && tv_align a1 a2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>= 
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2 
    else None
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else rtv_smem Ps1 Ps2 fid r (smem_alloca sm1 t1 st1 a1) sm2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    if tv_typ t1 t2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>= 
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2
    else None
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then
      rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else 
      if load_from_metadata sm2 st2 then
        rtv_smem Ps1 Ps2 fid r (smem_load sm1 t1 st1 a1) sm2
      else None
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_sterm Ps1 Ps2 fid r st11 st21 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r st12 st22 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else 
      if store_to_ret Ps1 Ps2 (rename_fid fid) st22 then
        rtv_smem Ps1 Ps2 fid r (smem_store sm1 t1 st11 st12 a1) sm2
      else None
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    if (eq_id fid1 fid2)
    then 
      rtv_list_sterm Ps1 Ps2 fid r sts1 sts2 >>=
      fun r => rtv_smem Ps1 Ps2 fid r sm1 sm2
    else rtv_smem Ps1 Ps2 fid r (smem_lib sm1 fid1 sts1) sm2
| (sm1, smem_lib sm2 lid sts) => 
    if smem_lib_sub lid then rtv_smem Ps1 Ps2 fid r sm1 sm2 else None
| (sm1, smem_alloca sm2 t2 st2 a2) => rtv_smem Ps1 Ps2 fid r sm1 sm2
| (sm1, smem_load sm2 t2 st2 a2) => 
  (* We check load_from_metadata to ensure that the behavior of output programs 
   * preserves input's. If we did not check, the additional load may be stuck. 
   *)
    if load_from_metadata sm2 st2 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2
    else None
| (sm1, smem_store sm2 t2 st21 st22 a2) => 
  (* We check that the additional stores must be to shadow_ret. *)
    if store_to_ret Ps1 Ps2 (rename_fid fid) st22 then
      rtv_smem Ps1 Ps2 fid r sm1 sm2
    else None
| _ => None
end.

Fixpoint rtv_sframe Ps1 Ps2 fid r (sf1 sf2:sframe) : option renaming :=
match (sf1, sf2) with
| (sframe_init, _) => Some r
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    if (tv_typ t1 t2 && tv_align a1 a2)
    then 
      rtv_smem Ps1 Ps2 fid r sm1 sm2 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
      fun r => rtv_sframe Ps1 Ps2 fid r sf1 sf2
    else rtv_sframe Ps1 Ps2 fid r (sframe_alloca sm1 sf1 t1 st1 a1) sf2
| _ => None
end.

(* Find a (id2,st2) from sm2 where st1 = st2, then return a new renaming. *)
Fixpoint match_smap Ps1 Ps2 fid r id1 st1 sm2 : option renaming :=
match sm2 with
| nil => None
| (id2,st2)::sm2' => 
    match rtv_sterm Ps1 Ps2 fid r st1 st2 with
    | Some r' => Some ((id1,id2)::r')
    | None => match_smap Ps1 Ps2 fid r id1 st1 sm2'
    end
end.

Fixpoint rtv_smap Ps1 Ps2 fid r (sm1 sm2:smap) : option renaming :=
match sm1 with
| nil => Some r
| (id1,st1)::sm1' =>
  match lookup_renaming r id1 with
  | Some id2 =>
    match lookupAL _ sm2 id2 with
    | None => None
    | Some st2 => 
        rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
        fun r => rtv_smap Ps1 Ps2 fid r sm1' sm2
    end
  | None => 
    match_smap Ps1 Ps2 fid r id1 st1 sm2 >>=
    fun r' => rtv_smap Ps1 Ps2 fid r' sm1' sm2
  end
end.

Definition rsub_sstate Ps1 Ps2 fid r s1 s2 : option renaming := 
if sumbool2bool _ _ (sterms_dec s1.(SEffects) s2.(SEffects)) then
  rtv_smap Ps1 Ps2 fid r s1.(STerms) s2.(STerms) >>=
  fun r => rtv_smem Ps1 Ps2 fid r s1.(SMem) s2.(SMem) >>=
  fun r => rtv_sframe Ps1 Ps2 fid r s1.(SFrame) s2.(SFrame)
else None.

Definition rtv_cmds Ps1 Ps2 fid r (nbs1 nbs2 : list nbranch) :=
rsub_sstate Ps1 Ps2 fid r (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2).

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Fixpoint rtv_sparams Ps1 Ps2 fid r (tsts1 tsts2:list (typ*attributes*sterm)) : 
  option renaming :=
match (tsts1, tsts2) with
| (nil, _) => Some r
| ((t1,_,st1)::tsts1', (t2,_,st2)::tsts2') => 
  if tv_typ t1 t2 then
    rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
    fun r => rtv_sparams Ps1 Ps2 fid r tsts1' tsts2'
  else None
| _ => None
end.

Definition rtv_scall Ps1 Ps2 fid r (c1:scall) (c2:sicall) : option renaming :=
  let '(stmn_call rid1 nr1 _ ty1 t1 tsts1) := c1 in
  match c2 with
  | stmn_icall_nptr rid2 nr2 _ ty2 t2 tsts2 =>
    if ((sumbool2bool _ _ (noret_dec nr1 nr2)) && tv_typ ty1 ty2) then
      rtv_sparams Ps1 Ps2 fid r tsts1 tsts2 >>=
      fun r => rtv_sterm Ps1 Ps2 fid r (remove_cast t1) (remove_cast t2) >>=
      fun r => Some ((rid1,rid2)::r)
    else None
  | stmn_icall_ptr _ _ _ ty2 t2 tsts2 _ _ rid2 _ _ _ _ _ _ _=>
    match ty1 with
    | typ_pointer _ =>
      if (tv_typ ty1 ty2) then
        rtv_sparams Ps1 Ps2 fid r tsts1 tsts2 >>=
        fun r => 
          match (remove_cast t1, remove_cast t2) with
          | (sterm_val (value_const (const_gid _ fid1)),
             sterm_val (value_const (const_gid _ fid2))) =>
             if tv_fid fid1 fid2 then Some ((rid1,rid2)::r) else None
          | (st1, st2) => 
              rtv_sterm Ps1 Ps2 fid r st1 st2 >>=
              fun r => Some ((rid1,rid2)::r)
          end
      else None
    | _ => None
    end
  end.

Definition rtv_subblock Ps1 Ps2 fid r (sb1:subblock) (sb2:SBsyntax.subblock) : 
  option renaming :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, SBsyntax.mkSB nbs2 call2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_icall st2 call2 in
  rsub_sstate Ps1 Ps2 fid r st1 st2 >>=
  fun r => rtv_scall Ps1 Ps2 fid r cl1 cl2 
end.

Fixpoint rtv_subblocks Ps1 Ps2 fid r (sbs1:list subblock) 
  (sbs2:list SBsyntax.subblock) : option renaming :=
match (sbs1, sbs2) with
| (nil, nil) => Some r
| (sb1::sbs1', sb2::sbs2') => 
    rtv_subblock Ps1 Ps2 fid r sb1 sb2 >>=
    fun r => rtv_subblocks Ps1 Ps2 fid r sbs1' sbs2'
| _ => None
end.

Fixpoint rtv_list_value_l r (vls1 vls2:list_value_l) : option renaming :=
match (vls1, vls2) with
| (Nil_list_value_l, Nil_list_value_l) => Some r
| (Cons_list_value_l v1 l1 vls1, Cons_list_value_l v2 l2 vls2) =>
    if eq_l l1 l2 then
      rtv_value r v1 v2 >>=
      fun r => rtv_list_value_l r vls1 vls2
    else None
| _ => None
end.

Definition rtv_phinode r t1 vls1 t2 vls2 : option renaming :=
if tv_typ t1 t2 then rtv_list_value_l r vls1 vls2 else None.

Fixpoint match_phinodes r i1 t1 vls1 ps2 : option (phinodes * renaming) :=
match ps2 with
| nil => None
| (insn_phi i2 t2 vls2)::ps2' => 
    if (is_tmp_var i2) then
      (* We assume phi tmp is always mapped to phi tmp *)
      match rtv_phinode r t1 vls1 t2 vls2 with
      | Some r' => Some (ps2',(i1,i2)::r')
      | None => match_phinodes r i1 t1 vls1 ps2'
      end
    else match_phinodes r i1 t1 vls1 ps2'
end.

Fixpoint rtv_phinodes r (ps1 ps2:phinodes) : option renaming :=
match ps1 with
| nil => Some r
| (insn_phi i1 t1 vls1)::ps1' =>
  match lookup_renaming r i1 with
  | Some i2 =>
    match lookupPhinode ps2 i2 with
    | None => None
    | Some (insn_phi _ t2 vls2) => 
      rtv_phinode r t1 vls1 t2 vls2 >>=
      fun r' => rtv_phinodes r ps1' ps2
    end
  | None =>
    match match_phinodes r i1 t1 vls1 ps2 with
    | None => None
    | Some (ps2',r') => rtv_phinodes r' ps1' ps2'
    end
  end
end.

Definition rtv_terminator r (tmn1 tmn2:terminator) : option renaming :=
match (tmn1, tmn2) with
| (insn_return id1 t1 v1, insn_return id2 t2 v2) => 
    if tv_typ t1 t2 then rtv_value r v1 v2 else None
| (insn_return_void id1, insn_return_void id2) => Some r
| (insn_br id1 v1 l11 l12, insn_br id2 v2 l21 l22) =>
    if eq_l l11 l21 && eq_l l12 l22 then rtv_value r v1 v2 else None
| (insn_br_uncond id1 l1, insn_br_uncond id2 l2) =>
    if eq_l l1 l2 then Some r else None
| (insn_unreachable id1, insn_unreachable id2) => Some r
| _ => None
end.

Definition rtv_block Ps1 Ps2 fid r (b1:block) (b2:SBsyntax.block) 
  : option renaming :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, SBsyntax.block_common l2 ps2 sbs2 nbs2 tmn2) =>
  match cmds2sbs cs1 with
  | (sbs1, nbs1) =>
    if eq_l l1 l2 then
      rtv_phinodes r ps1 ps2 >>=
      fun r => rtv_subblocks Ps1 Ps2 fid r sbs1 sbs2 >>=
      fun r => rtv_cmds Ps1 Ps2 fid r nbs1 nbs2 >>=
      fun r => rtv_terminator r tmn1 tmn2
    else None
  end 
| (block_intro l1 ps1 cs1 tmn1, SBsyntax.block_ret_ptr l2 ps2 sbs2 nbs2
    (SBsyntax.insn_return_ptr _ _ _ _ _ _ _ _ _ _ vp _ _ _ _)) =>
  match cmds2sbs cs1 with
  | (sbs1, nbs1) =>
    if eq_l l1 l2 then
      rtv_phinodes r ps1 ps2 >>=
      fun r => rtv_subblocks Ps1 Ps2 fid r sbs1 sbs2 >>=
      fun r => rtv_cmds Ps1 Ps2 fid r nbs1 nbs2 >>=
      fun r =>
        match tmn1 with
        | insn_return id1 _ v1 => rtv_value r v1 vp
        | _ => None
        end
    else None
  end 
end.

Fixpoint rtv_blocks Ps1 Ps2 fid r (bs1:blocks) (bs2:SBsyntax.blocks):=
match (bs1, bs2) with
| (nil, nil) => Some r
| (b1::bs1', b2::bs2') => 
    rtv_block Ps1 Ps2 fid r b1 b2 >>=
    fun r => rtv_blocks Ps1 Ps2 fid r bs1' bs2'
| _ => None
end.

Definition rtv_fdef nts1 Ps1 Ps2 (f1:fdef) (f2:SBsyntax.fdef) :=
match (f1, f2) with
| (fdef_intro (fheader_intro _ _ fid1 _ _ as fh1) lb1, 
   SBsyntax.fdef_intro fh2 lb2) =>
  match rtv_blocks Ps1 Ps2 fid1 nil lb1 lb2 with
  | None => false
  | Some _ => tv_fheader nts1 fh1 fh2 
  end
end.

Fixpoint rtv_products nts1 (Ps10 Ps1:products) (Ps2:SBsyntax.products) : bool :=
match Ps1 with
| nil => true
| product_gvar gv1::Ps1' =>
  match SBsyntax.lookupGvarViaIDFromProducts Ps2 (getGvarID gv1) with
  | None => false
  | Some gv2 => sumbool2bool _ _ (gvar_dec gv1 gv2) && 
                rtv_products nts1 Ps10 Ps1' Ps2 
  end
| product_fdec f1::Ps1' =>
  match SBsyntax.lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1)) with
  | None => false
  | Some f2 => tv_fdec nts1 f1 f2 && rtv_products nts1 Ps10 Ps1' Ps2 
  end
| product_fdef f1::Ps1' =>
  match SBsyntax.lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1)) with
  | None => false
  | Some f2 => rtv_fdef nts1 Ps10 Ps2 f1 f2 && rtv_products nts1 Ps10 Ps1' Ps2 
  end
end.

Definition rtv_module (m1:module) (m2:SBsyntax.module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, SBsyntax.module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  rtv_products nts1 Ps1 Ps1 Ps2
end.

(*************************************)
(* MTV *)

(* 
   ptr = load addr_of_ptr
   hashLoadBaseBound addr_of_ptr addr_of_b addr_of_e _ _ _
*)
Fixpoint deref_from_metadata (fid:id) (sm:smem) (addr_of_b addr_of_e ptr:sterm) 
  : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_free sm1 _ _ => false
| smem_load sm1 _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_store sm1 _ _ _ _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
| smem_lib sm1 fid1 sts1 =>
    if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm addr_of_ptr 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm _ Nil_list_sterm))))) =>
      if (eq_sterm_upto_cast addr_of_b addr_of_base &&
          eq_sterm_upto_cast addr_of_e addr_of_bound) then
        match (remove_cast addr_of_ptr, remove_cast ptr) with
        | (st1, sterm_load _ _ st2 _) => eq_sterm_upto_cast st1 st2
        | _ => false
        end
      else deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    | _ => deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
    end      
    else deref_from_metadata fid sm1 addr_of_b addr_of_e ptr
end.

Definition metadata := list (id*l*nat*id*id*id*bool).

Fixpoint is_metadata_aux (ms:metadata) (fid:id) (l1:l) (i:nat) (b e p:id) im 
  : bool :=
match ms with
| nil => false
| (fid',l2,i',b',e',p',im')::ms' => 
    (eq_id fid fid' && eq_l l1 l2 && beq_nat i i' && eq_id b b' && eq_id e e' &&
     eq_id p p' && eqb im im') ||
    is_metadata_aux ms' fid l1 i b e p im
end.

(* We assume there is a way to know the mapping between
     function id, block, base, bound, ptr and flag *)
Axiom get_metadata : unit -> metadata.

Definition is_metadata (fid:id) (l1:l) (i:nat) (b e p:id) (im:bool) : bool :=
  is_metadata_aux (get_metadata tt) fid l1 i b e p im.

Fixpoint check_mptr_metadata_aux (Ps2:SBsyntax.products) fid l1 i base bound ptr
  := 
match (base, bound, ptr) with
| (sterm_val (value_id idb), sterm_val (value_id ide), 
   sterm_val (value_id idp)) => 
    is_metadata fid l1 i idb ide idp true
| (sterm_malloc _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sz_sterm _ st20 Nil_list_sz_sterm),  
   sterm_malloc _ _ _ _ as st3) =>
     eq_sterm_upto_cast st1 st2 && 
     eq_sterm_upto_cast st1 st3 && 
     eq_sterm st10 st20
| (sterm_alloca _ _ st10 _ as st1, 
   sterm_gep _ _ st2 (Cons_list_sz_sterm _ st20 Nil_list_sz_sterm),  
   sterm_alloca _ _ _ _ as st3) =>
     eq_sterm_upto_cast st1 st2 && 
     eq_sterm_upto_cast st1 st3 && 
     eq_sterm st10 st20
| (sterm_val (value_const (const_gid _ _ as c1)),
   sterm_val (value_const (const_gep _ (const_gid _ _ as c2)
     (Cons_list_const (const_int _ i2) Nil_list_const))),  
   sterm_val (value_const (const_gid _ _ as c3))) =>
     eq_const c1 c2 && eq_const c1 c3 && eq_INT_Z i2 1%Z   
| (sterm_load sm1 _ st1 _, sterm_load sm2 _ st2 _, st3) =>
     deref_from_metadata fid sm1 st1 st2 st3
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22,
   sterm_select st30 _ st31 st32) =>
     eq_sterm st10 st20 && eq_sterm st20 st30 &&
     check_mptr_metadata_aux Ps2 fid l1 i st11 st21 st31 && 
     check_mptr_metadata_aux Ps2 fid l1 i st12 st22 st32
(*
  Assign external globals infinite base/bound.

  %bcast_ld_dref_base19 = bitcast i8* null to i8* 
  %16 = bitcast i8* inttoptr (i32 2147483647 to i8* ) to i8*
  %bcast_ld_dref_bound20 = bitcast %struct._IO_FILE** @stderr to i8* 
*)
| (sterm_val (value_const (const_null t0)),
   sterm_val (value_const (const_castop castop_inttoptr (const_int _ i0) t1)),
   sterm_val (value_const (const_gid (typ_pointer (typ_pointer _)) id))) =>
     tv_typ t0 t1 && tv_typ t0 (typ_pointer (typ_int Size.Eight)) &&
     eq_INT_Z i0 (two_p 48%Z) &&
     match SBsyntax.lookupGvarFromProducts Ps2 id with 
     | Some (gvar_external _ _ _) => true
     | _ => false
     end
| (sterm_val (value_const (const_null _)), 
   sterm_val (value_const (const_null _)),
   sterm_cast castop_inttoptr _ _ _) => true (* int2ptr *)
| (sterm_val (value_const (const_null _)), 
   sterm_val (value_const (const_null _)),
   sterm_val (value_const (const_null _))) => true
| (sterm_val (value_const (const_undef _)),
   sterm_val (value_const (const_undef _)),
   sterm_val (value_const (const_undef _))) => true (* assumed by Softbound *)
| _ => false
end.

Definition check_mptr_metadata (Ps2:SBsyntax.products) fid l1 i base bound ptr 
  := 
  check_mptr_metadata_aux Ps2 fid l1 i (remove_cast base) (remove_cast bound) 
    (get_ptr_object ptr).

Fixpoint check_fptr_metadata_aux (Ps2:SBsyntax.products) fid l1 i base bound ptr
  := 
match (base, bound, ptr) with
| (sterm_val (value_id idb), sterm_val (value_id ide), 
   sterm_val (value_id idp)) => 
    is_metadata fid l1 i idb ide idp false
| (sterm_load sm1 _ st1 _, sterm_load sm2 _ st2 _, st3) =>
     deref_from_metadata fid sm1 st1 st2 st3
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22,
   sterm_select st30 _ st31 st32) =>
     eq_sterm st10 st20 && eq_sterm st20 st30 &&
     check_fptr_metadata_aux Ps2 fid l1 i st11 st21 st31 && 
     check_fptr_metadata_aux Ps2 fid l1 i st12 st22 st32
| (sterm_val (value_const (const_gid _ id1)),
   sterm_val (value_const (const_gid _ id2)),
   sterm_val (value_const (const_gid _ id3))) => (*fptr*)
   match SBsyntax.lookupFdecFromProducts Ps2 id1 with 
   | Some _ => eq_id id1 id2 && eq_id id2 id3
   | _ => false
   end
| _ => false
end.

Definition check_fptr_metadata (Ps2:SBsyntax.products) fid l1 i base bound ptr 
  := 
  check_fptr_metadata_aux Ps2 fid l1 i (remove_cast base) (remove_cast bound) 
    (remove_cast ptr).

Definition check_metadata (Ps2:SBsyntax.products) fid l1 i base bound ptr 
  (im:bool) := 
  if im then check_mptr_metadata Ps2 fid l1 i base bound ptr
  else check_fptr_metadata Ps2 fid l1 i base bound ptr. 

Definition deref_check Ps2 fid l1 i lid sts : bool :=
  if (is_loadStoreDereferenceCheck lid) then
    match sts with
    |  Cons_list_sterm base 
      (Cons_list_sterm bound
      (Cons_list_sterm ptr
      (Cons_list_sterm size_of_type
      (Cons_list_sterm _ Nil_list_sterm)))) => 
        check_mptr_metadata Ps2 fid l1 i base bound ptr
    | _ => false
    end
  else if (is_callDereferenceCheck lid) then
    match sts with
    |  Cons_list_sterm base 
      (Cons_list_sterm bound
      (Cons_list_sterm ptr Nil_list_sterm)) => 
        check_fptr_metadata Ps2 fid l1 i base bound ptr
    | _ => false
    end
  else true.

(* 
   store ptr addr_of_ptr
   hashStoreBaseBound addr_of_ptr b e _ _ _
*)
Fixpoint find_stored_ptr sm addr_of_ptr : option sterm :=
match sm with
| smem_init => None
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_lib sm1 _ _ => find_stored_ptr sm1 addr_of_ptr
| smem_store sm1 _ st1 st2 _ =>
    if (eq_sterm_upto_cast st2 addr_of_ptr) then Some st1
    else find_stored_ptr sm1 addr_of_ptr
end.

Fixpoint store_to_metadata (Ps2:SBsyntax.products) fid l1 i sm (lid:id) sts 
  : bool :=
if (is_hashLoadBaseBound lid) then
  match sts with
  |  Cons_list_sterm addr_of_ptr 
    (Cons_list_sterm base
    (Cons_list_sterm bound
    (Cons_list_sterm _
    (Cons_list_sterm _
    (Cons_list_sterm _ Nil_list_sterm))))) =>
      match (find_stored_ptr sm addr_of_ptr) with
      | None => false
      | Some ptr => check_mptr_metadata Ps2 fid l1 i base bound ptr ||
          check_fptr_metadata Ps2 fid l1 i base bound ptr
      end
  | _ => false
  end      
else true.

(* We assume there is a way to know the mapping between
     function id, addr_of_base, and addr_of_bound used by __hashLoadBaseBound
*)
Axiom get_addrof_be : unit -> list (id * id * id).

Fixpoint is_addrof_be_aux (abes:list (id*id*id)) (fid ab ae:id)
  : bool :=
match abes with
| nil => false
| (fid', ab', ae')::abes' => 
    if (eq_id fid fid' && eq_id ab ab' && eq_id ae ae') then true
    else is_addrof_be_aux abes' fid ab ae
end.

Definition is_addrof_be (fid:id) (sab sae:sterm) : bool :=
match (sab, sae) with
| (sterm_val (value_id ab), sterm_val (value_id ae)) =>
  is_addrof_be_aux (get_addrof_be tt) fid ab ae
| (sterm_alloca _ _ _ _, sterm_alloca _ _ _ _) => true
| _ => false
end.

(* ptr is safe to access if ptr is asserted by a deref check or
   from hasLoadBaseBound *)
Fixpoint safe_mem_access fid (sm:smem) t (ptr:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => safe_mem_access fid sm1 t ptr
| smem_lib sm1 fid1 sts1 =>
  if (is_loadStoreDereferenceCheck fid1) then
    match sts1 with
    |  Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm actual_ptr
      (Cons_list_sterm
         (sterm_val 
           (value_const 
             (const_castop 
               castop_ptrtoint
               (const_gep false 
                 (const_null t) 
                   (Cons_list_const (const_int _ i0) Nil_list_const)
               )
              (typ_int sz)
             )
           )
         )
      (Cons_list_sterm _ Nil_list_sterm)))) =>
      if (eq_sterm (get_ptr_object ptr) (get_ptr_object actual_ptr) && 
         eq_INT_Z i0 1%Z && 
         sumbool2bool _ _ (Size.dec sz Size.ThirtyTwo))
      then true else safe_mem_access fid sm1 t ptr
    | _ => safe_mem_access fid sm1 t ptr
    end
  else if (is_hashLoadBaseBound fid1) then
    match sts1 with
    |  Cons_list_sterm _ 
      (Cons_list_sterm addr_of_base
      (Cons_list_sterm addr_of_bound
      (Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm ptr_safe Nil_list_sterm))))) =>
      if (eq_sterm ptr addr_of_base || 
          eq_sterm ptr addr_of_bound || 
          eq_sterm ptr ptr_safe) 
      then is_addrof_be fid addr_of_base addr_of_bound  
      else safe_mem_access fid sm1 t ptr
    | _ => safe_mem_access fid sm1 t ptr
    end
  else safe_mem_access fid sm1 t ptr
end.

Fixpoint sterm_is_memsafe (Ps1:products) (Ps2:SBsyntax.products) fid l i 
  (st:sterm) : bool :=
match st with
| sterm_val v => true
| sterm_bop _ _ st1 st2 
| sterm_fbop _ _ st1 st2  
| sterm_icmp _ _ st1 st2 
| sterm_fcmp _ _ st1 st2 
| sterm_insertvalue _ st1 _ st2 _ => 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && sterm_is_memsafe Ps1 Ps2 fid l i st2 
| sterm_trunc _ _ st1 _
| sterm_ext _ _ st1 _ 
| sterm_cast _ _ st1 _ 
| sterm_extractvalue _ st1 _ => sterm_is_memsafe Ps1 Ps2 fid l i st1
| sterm_malloc sm _ st1 _
| sterm_alloca sm _ st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm && sterm_is_memsafe Ps1 Ps2 fid l i st1
| sterm_load sm t st1 _ => 
   smem_is_memsafe Ps1 Ps2 fid l i sm && sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
   safe_mem_access fid sm t st1
| sterm_gep _ _ st1 sts2 => 
   sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
   list_sz_sterm_is_memsafe Ps1 Ps2 fid l i sts2
| sterm_phi _ stls => list_sterm_l_is_memsafe Ps1 Ps2 fid l i stls
| sterm_select st1 _ st2 st3 => 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st2 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st3
| sterm_lib sm lid sts => 
    smem_is_memsafe Ps1 Ps2 fid l i sm && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts && 
    store_to_metadata Ps2 fid l i sm lid sts
end
with list_sz_sterm_is_memsafe Ps1 (Ps2:SBsyntax.products) fid l i 
  (sts:list_sz_sterm) : bool :=
match sts with
| Nil_list_sz_sterm => true
| Cons_list_sz_sterm _ st sts0 => 
    sterm_is_memsafe Ps1 Ps2 fid l i st && 
    list_sz_sterm_is_memsafe Ps1 Ps2 fid l i sts0
end
with list_sterm_is_memsafe Ps1 (Ps2:SBsyntax.products) fid l i (sts:list_sterm) 
  : bool :=
match sts with
| Nil_list_sterm => true
| Cons_list_sterm st sts0 => 
    sterm_is_memsafe Ps1 Ps2 fid l i st && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts0
end
with list_sterm_l_is_memsafe Ps1 (Ps2:SBsyntax.products) fid l i 
  (stls:list_sterm_l) : bool :=
match stls with
| Nil_list_sterm_l => true
| Cons_list_sterm_l st _ stls0 =>
    sterm_is_memsafe Ps1 Ps2 fid l i st && 
    list_sterm_l_is_memsafe Ps1 Ps2 fid l i stls0
end
with smem_is_memsafe (Ps1:products) (Ps2:SBsyntax.products) fid l i (sm:smem) 
  : bool :=
match sm with
| smem_init => true
| smem_malloc sm1 _ st1 _
| smem_alloca sm1 _ st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && sterm_is_memsafe Ps1 Ps2 fid l i st1
| smem_free sm1 _ _ => false
| smem_load sm1 t st1 _ => 
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st1 && 
    safe_mem_access fid sm1 t st1
| smem_store sm1 t st11 st12 _ =>
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st11 && 
    sterm_is_memsafe Ps1 Ps2 fid l i st12 && 
    (store_to_ret Ps1 Ps2 fid st12 || 
     safe_mem_access fid sm1 (typ_pointer t) st12)
| smem_lib sm1 lid1 sts1 =>
    smem_is_memsafe Ps1 Ps2 fid l i sm1 && 
    list_sterm_is_memsafe Ps1 Ps2 fid l i sts1 && 
    deref_check Ps2 fid l i lid1 sts1
end.

Fixpoint check_all_metadata_aux (Ps2:SBsyntax.products) fid l1 i1 (sm:smap) 
  (ms:metadata) : bool :=
match ms with
| nil => true
| (fid0,l2,i2,b,e,p,im)::ms' =>
    (if (eq_id fid0 fid && eq_l l1 l2 && beq_nat i1 i2) then
      match (lookupAL _ sm b, lookupAL _ sm e, lookupAL _ sm p) with
      | (Some sb, Some se, Some sp) => check_metadata Ps2 fid l1 i1 sb se sp im
      | (Some sb, Some se, None) => 
          (* 
             l1:  
               p = malloc; b = p; e = p + size;
             l2
               b1 = bitcast b; e1 = bitcast e
               and p is falled-through or  
          *)
          check_metadata Ps2 fid l1 i1 sb se (sterm_val (value_id p)) im
      | (None, None, Some (sterm_gep _ _ _ _)) => 
          (*   
             l1:  
               p = malloc; b = p; e = p + size;
             l2:
               b and e are falled-through  
               q = gep p ...
          *)
          true
      | (None, None, None) => 
          (*   b, e and p are falled-through  *)
          true
      | _ => false
      end
    else true) &&
    check_all_metadata_aux Ps2 fid l1 i1 sm ms'
end.

Definition check_all_metadata (Ps2:SBsyntax.products) fid l i sm :=
  check_all_metadata_aux Ps2 fid l i sm (get_metadata tt).

Fixpoint check_addrof_be_aux fid (sm:smap) (abes:list (id*id*id))
  : bool :=
match abes with
| nil => true
| (fid0,ab,ae)::abes' =>
    (if (eq_id fid0 fid) then
      match (lookupAL _ sm ab, lookupAL _ sm ae) with
      | (None, None) => true
      | (Some (sterm_alloca _ _ _ _), Some (sterm_alloca _ _ _ _)) => true
      | _ => false
      end
    else true) &&
    check_addrof_be_aux fid sm abes'
end.

Definition check_addrof_be fid sm :=
  check_addrof_be_aux fid sm (get_addrof_be tt).

Definition mtv_cmds Ps1 Ps2 fid l (nbs2 : list nbranch) :=
let st2 := se_cmds sstate_init nbs2 in 
smem_is_memsafe Ps1 Ps2 fid l O st2.(SMem) &&
check_all_metadata Ps2 fid l O st2.(STerms) &&
check_addrof_be fid st2.(STerms).

Fixpoint mtv_func_metadata (ms:metadata) (Ps2:SBsyntax.products) fid l1 i1 fid2 
  ars2 sars2 : bool :=
match ms with
| nil => true
| (fid0,l2,i2,b,e,p,im)::ms' =>
    (if (eq_id fid0 fid2 && eq_l l2 (l_of_arg tt) && beq_nat i2 O) then
      match (lookupSarg ars2 sars2 b, lookupSarg ars2 sars2 e, 
        lookupSarg ars2 sars2 p) with
      | (Some sb, Some se, Some sp) => check_metadata Ps2 fid l1 i1 sb se sp im
      | _ => false
      end
    else true) &&
    mtv_func_metadata ms' Ps2 fid l1 i1 fid2 ars2 sars2
end.

(*
  fid2 args2

  fid
  ...
    l1:
      call fid2 tsts2   
*)
(* function ptr is safe to access if ptr is asserted by a deref check *)
Fixpoint safe_fptr_access_aux (sm:smem) (ptr:sterm) : bool :=
match sm with
| smem_init => false
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _
| smem_store sm1 _ _ _ _ => safe_fptr_access_aux sm1 ptr
| smem_lib sm1 fid1 sts1 =>
  if (is_callDereferenceCheck fid1) then
    match sts1 with
    |  Cons_list_sterm _
      (Cons_list_sterm _
      (Cons_list_sterm actual_ptr Nil_list_sterm)) =>
      if (eq_sterm_upto_cast ptr actual_ptr)
      then true else safe_fptr_access_aux sm1 ptr
    | _ => safe_fptr_access_aux sm1 ptr
    end
  else safe_fptr_access_aux sm1 ptr
end.

Definition safe_fptr_access (sm:smem) (ptr:sterm) : bool :=
match ptr with
| sterm_val (value_const (const_gid _ fid2)) => true
| _ => safe_fptr_access_aux sm ptr
end.

Definition mtv_iscall (Ps2:SBsyntax.products) fid l1 i1 sm (c2:sicall) :=
match c2 with
| stmn_icall_nptr _ _ _ _ t2 tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) as st2 =>
      if (isCallLib fid2) then true
      else
        match (SBsyntax.lookupFdefViaIDFromProducts Ps2 fid2) with
        | None => true
        | Some (SBsyntax.fdef_intro (fheader_intro _ _ _ args2 _) _) =>
            mtv_func_metadata (get_metadata tt) Ps2 fid l1 i1 fid2 args2 tsts2
        end
  | _ => true
  end && safe_fptr_access sm t2
| stmn_icall_ptr _ _ _ _ t2 tsts2 _ _ _ _ _ _ _ _ _ _=>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) as st2 =>
      if (isCallLib fid2) then true
      else
        match (SBsyntax.lookupFdefViaIDFromProducts Ps2 fid2) with
        | Some (SBsyntax.fdef_intro (fheader_intro _ _ _ (_::args2) _) _) =>
            mtv_func_metadata (get_metadata tt) Ps2 fid l1 i1 fid2 args2 tsts2
        | _ => true
        end
  | _ => true
  end && safe_fptr_access sm t2
end.

Definition mtv_subblock Ps1 Ps2 fid l nth (sb2:SBsyntax.subblock) :=
match sb2 with
| SBsyntax.mkSB nbs2 call2 =>
  let st2 := se_cmds sstate_init nbs2 in
  let cl2 := se_icall st2 call2 in
   smem_is_memsafe Ps1 Ps2 fid l nth st2.(SMem) &&
   check_all_metadata Ps2 fid l nth st2.(STerms) &&
   check_addrof_be fid st2.(STerms) &&
   mtv_iscall Ps2 fid l nth st2.(SMem) cl2
end.

Fixpoint mtv_subblocks_aux Ps1 Ps2 fid l len (sbs2:list SBsyntax.subblock) :=
match sbs2 with
| nil => true
| sb2::sbs2' => 
    mtv_subblock Ps1 Ps2 fid l (len - List.length sbs2') sb2 && 
    mtv_subblocks_aux Ps1 Ps2 fid l len sbs2'
end.

Definition mtv_subblocks Ps1 Ps2 fid l (sbs2:list SBsyntax.subblock) :=
  mtv_subblocks_aux Ps1 Ps2 fid l (List.length sbs2) (List.rev sbs2).

(* Check
   1) i = phi l1 i1, l2 i2, ..., ln in
      if i is a metadata, then all i1 ... in should be metadata
   2) i = phi l1 i1, l2 i2, ..., ln in
      i' = phi l1' i1', l2' i2', ..., lm' im'
      if both i and i' are metadata, l1 ... ln should be a permutation of 
         l1' ... lm'
   3) either all of (b e p) are in phinodes, or none of them is...
   Not clear how to implement the checking in a way suitable to proofs.
*)

Definition mtv_bep_value (Ps2:SBsyntax.products) fid l1 (bv ev pv:value) im 
  : bool :=
match (bv, ev, pv) with
| (value_id bid, value_id eid, value_id pid) => 
    is_metadata fid l1 O bid eid pid im
| (value_const (const_gid _ _ as c1),
   value_const (const_gep _ (const_gid _ _ as c2)
     (Cons_list_const (const_int _ i2) Nil_list_const)),  
   value_const (const_gid _ _ as c3)) =>
     eq_const c1 c2 && eq_const c1 c3 && eq_INT_Z i2 1%Z   
| (value_const (const_null t0),
   value_const (const_castop castop_inttoptr (const_int _ i0) t1),
   value_const (const_gid (typ_pointer (typ_pointer _)) id)) =>
     tv_typ t0 t1 && tv_typ t0 (typ_pointer (typ_int Size.Eight)) &&
     eq_INT_Z i0 (two_p 48%Z) &&
     match SBsyntax.lookupGvarFromProducts Ps2 id with 
     | Some (gvar_external _ _ _) => true
     | _ => false
     end
| (value_const (const_null _), 
   value_const (const_null _),
   value_const (const_castop castop_inttoptr _ _)) => true
| (value_const (const_null _), value_const (const_null _), 
    value_const (const_null _)) => true
| (value_const (const_undef _), value_const (const_undef _), 
     value_const (const_undef _)) => 
    (* I dont think this is safe, since undefined values can be
       arbitrary. But Softbound assumes the this is fine. *)
    true
| (value_const (const_gid _ id1),
   value_const (const_gid _ id2),
   value_const (const_gid _ id3)) => (*fptr*)
   match SBsyntax.lookupFdecFromProducts Ps2 id1 with 
   | Some _ => eq_id id1 id2 && eq_id id2 id3
   | _ => false
   end
| _ => false
end.

Fixpoint mtv_list_value_l Ps2 fid (bvls evls pvls:list_value_l) im : bool :=
match bvls with
| Nil_list_value_l => true
| Cons_list_value_l bv bl bvls' =>
    match (getValueViaLabelFromValuels evls bl,
           getValueViaLabelFromValuels pvls bl) with
    | (Some ev, Some pv) => mtv_bep_value Ps2 fid bl bv ev pv im
    | _ => false
    end && mtv_list_value_l Ps2 fid bvls' evls pvls im
end.

Fixpoint mtv_phinodes_aux Ps2 fid l1 i1 (ms:metadata) (ps2:phinodes) : bool :=
match ms with
| nil => true
| (fid',l2,i2,b,e,p,im)::ms' =>
    (if (eq_id fid fid' && eq_l l1 l2 && beq_nat i1 i2) then
       match (lookupPhinode ps2 b, lookupPhinode ps2 e, lookupPhinode ps2 p) with
       | (None, None, None) => true
       | (Some (insn_phi _ _ bvls), Some (insn_phi _ _ evls), 
           Some (insn_phi _ _ pvls)) => 
           mtv_list_value_l Ps2 fid bvls evls pvls im
       | _ => false
       end
     else true) && 
    mtv_phinodes_aux Ps2 fid l1 i1 ms' ps2 
end.

Definition mtv_phinodes Ps2 fid l i (ps2:phinodes) : bool :=
  mtv_phinodes_aux Ps2 fid l i (get_metadata tt) ps2.

Definition mtv_block Ps1 Ps2 fid (b2:SBsyntax.block) :=
match b2 with
| SBsyntax.block_common l2 ps2 sbs2 nbs2 tmn2 =>
    mtv_phinodes Ps2 fid l2 (S (List.length sbs2)) ps2 &&
    mtv_subblocks Ps1 Ps2 fid l2 sbs2 && mtv_cmds Ps1 Ps2 fid l2 nbs2
| SBsyntax.block_ret_ptr l2 ps2 sbs2 nbs2
    (SBsyntax.insn_return_ptr _ _ _ _ _ vb _ _ ve _ vp _ _ _ _) =>
    mtv_phinodes Ps2 fid l2 (S (List.length sbs2)) ps2 &&
    mtv_subblocks Ps1 Ps2 fid l2 sbs2 && mtv_cmds Ps1 Ps2 fid l2 nbs2 &&
    (mtv_bep_value Ps2 fid l2 vb ve vp true ||
     mtv_bep_value Ps2 fid l2 vb ve vp false)
end.

Fixpoint mtv_blocks Ps1 Ps2 fid (bs2:SBsyntax.blocks):=
match bs2 with
| nil => true
| b2::bs2' => mtv_block Ps1 Ps2 fid b2 && mtv_blocks Ps1 Ps2 fid bs2'
end.

Definition mtv_fdef Ps1 Ps2 (f2:SBsyntax.fdef) :=
match f2 with
| SBsyntax.fdef_intro ((fheader_intro _ t2 fid2 a2 _) as fh2) lb2 =>
  if (isCallLib fid2) then true else mtv_blocks Ps1 Ps2 fid2 lb2
end.

Fixpoint mtv_products Ps1 (Ps20 Ps2:SBsyntax.products) : bool :=
match Ps2 with
| nil => true
| SBsyntax.product_fdef f2::Ps2' => mtv_fdef Ps1 Ps20 f2 && 
    mtv_products Ps1 Ps20 Ps2'
| _::Ps2' => mtv_products Ps1 Ps20 Ps2'
end.

Definition mtv_module (m1:module) (m2:SBsyntax.module) :=
match (m1, m2) with
| (module_intro _ _ Ps1, SBsyntax.module_intro _ _ Ps2) => 
    mtv_products Ps1 Ps2 Ps2
end.

(***********************************)
(* tactic *)
Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_value _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_typ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_align _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_sterm _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_smem _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_id _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_const _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:eq_l _ _ = true |- _ ] => apply sumbool2bool_true in H
  end.

Ltac sumbool_subst :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_value _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:tv_typ _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:tv_align _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_sterm _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_smem _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_id _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_const _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  | [ H:eq_l _ _ = true |- _ ] => apply sumbool2bool_true in H; subst
  end.

Tactic Notation "sumbool_subst" "in" hyp(H) :=
  apply sumbool2bool_true in H.



(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
