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
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import sub_tv_def.
Require Import Coq.Bool.Sumbool.
Require Import monad.

Export SBSE.

(* true <-> id == @__hashLoadBaseBound *)
Axiom is_hashLoadBaseBound : id -> bool.

(* true <-> id == @__loadDereferenceCheck or @__storeDereferenceCheck 

void @__load(store)DereferenceCheck(
  i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe)
*)
Axiom is_loadStoreDereferenceCheck : id -> bool.

(* void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) *)
Axiom is_callDereferenceCheck : id -> bool.

(* true <-> id == @__hashStoreBaseBound *)
Axiom is_hashStoreBaseBound : id -> bool.

(***************************************************************)
(* Simplification w.r.t program equivalence. *)

(* cast does not change value. We can prove they have the same operational
 * semantics. *)
Fixpoint remove_cast_const (c:const) : const :=
match c with
| const_castop castop_bitcast c1 _ => remove_cast_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint remove_cast (st:sterm) : sterm :=
match st with
| sterm_cast castop_bitcast _ st1 _ => remove_cast st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (remove_cast st1)(remove_cast st2) 
| sterm_val (value_const c) => sterm_val (value_const (remove_cast_const c))
| _ => st
end.

(*
  return the object pointer, e.g.

  %2 = getelementptr i32* %ptr.05, i32 %i.04
  %bcast_ld_dref_bound = bitcast i32* %2 to i8*   

  We return %ptr.05.
*)
Fixpoint get_ptr_object_const (c:const) : const :=
match c with
| const_castop castop_bitcast c1 _ => get_ptr_object_const c1
| const_gep _ c1 _ => get_ptr_object_const c1
| const_select c0 c1 c2 => 
    const_select c0 (remove_cast_const c1)(remove_cast_const c2) 
| _ => c
end.

Fixpoint get_ptr_object (st:sterm) : sterm :=
match st with
| sterm_cast castop_bitcast _ st1 _ => get_ptr_object st1
| sterm_gep _ _ st1 _ => get_ptr_object st1
| sterm_select st0 t st1 st2 => 
    sterm_select st0 t (get_ptr_object st1)(get_ptr_object st2) 
| sterm_val (value_const c) => sterm_val (value_const (get_ptr_object_const c))
| _ => st
end.

Definition eq_sterm_upto_cast (st1 st2:sterm) : bool :=
eq_sterm (remove_cast st1) (remove_cast st2).

(************************************************************)
(* Generating metadata *) 

(* The label of arg. *)
Axiom l_of_arg : unit -> l.

(* base, bound, ptr, flag (true:mem ptr, false:fptr) *)
Definition beps := list (id * id * id * bool).
(*
   We assign indices for phi, subblocks and appendent cmds inside a block, like 
   phi_n+1 s_n s_n-1 ... s_2 s_1 c_0

   At the (l_of_arg tt) block there is one subblock --- the 0th.
 *)
Definition nbeps := list (nat * beps).
Definition lnbeps := list (l * nbeps).          (* block label * nbeps *)
Definition flnbeps := list (id * lnbeps).       (* function name * lnbeps *)

(* add b e p if they are not in md *)
Fixpoint add_bep (md:beps) (b e p:id) (im:bool): beps :=
match md with
| nil => [(b,e,p,im)]
| (b',e',p',im')::md' => 
    if (eq_id b b' && eq_id e e' && eq_id p p' && eqb im im') then md
    else (b',e',p',im')::add_bep md' b e p im
end.

Fixpoint add_beps (accum bep:beps): beps :=
match bep with
| nil => accum
| (b,e,p,im)::bep' =>
  add_beps (add_bep accum b e p im) bep'
end.

(* update if exists, add it otherwise *)
Fixpoint updateAdd_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => (i, gv)::nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::updateAdd_nbeps m' i gv
end.

(* update only if exists, do nothing otherwise *)
Fixpoint update_nbeps (m:nbeps) (i:nat) (gv:beps) : nbeps :=
match m with
| nil => nil
| (i', gv')::m' =>
  if (beq_nat i i')
  then (i', gv)::m'
  else (i', gv')::update_nbeps m' i gv
end.

Fixpoint lookup_nbeps (m:nbeps) (i:nat) : option beps :=
match m with
| nil => None
| (i', gv')::m' =>
  if (beq_nat i i')
  then Some gv'
  else lookup_nbeps m' i
end.

(* If assert(b<=e<p), and b e p are defined wrt open variables,
   add those open variables.

   Assumption:
   1) Used within a subblock
   2) b e p must be created all together
   3) Within a subblock, b e can only be bitcasted or selected, 
      p can only be gep-ed or selected. 
*)
Fixpoint metadata_from_bep_aux (base bound ptr:sterm) im (accum:beps) : beps :=
match (base, bound, ptr) with
| (sterm_val (value_id b), sterm_val (value_id e), sterm_val (value_id p)) => 
    add_bep accum b e p im
| (sterm_select st10 _ st11 st12, sterm_select st20 _ st21 st22, 
   sterm_select st30 _ st31 st32) =>
    if (eq_sterm st10 st20 && eq_sterm st20 st30) then
      metadata_from_bep_aux st11 st21 st31 im
        (metadata_from_bep_aux st12 st22 st32 im accum)
    else accum
| _ => accum
end.

Definition metadata_from_bep (base bound ptr:sterm) im (accum:beps) : beps :=
  metadata_from_bep_aux (remove_cast base) (remove_cast bound) 
    (get_ptr_object ptr) im accum.

Fixpoint metadata_from_smem (sm:smem) (accum:beps) : beps :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => metadata_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    metadata_from_smem sm1
    (if (is_loadStoreDereferenceCheck lid1) then
      match sts1 with
      |  Cons_list_sterm base 
        (Cons_list_sterm bound
        (Cons_list_sterm ptr
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm)))) => 
          metadata_from_bep base bound ptr true accum
      | _ => accum
      end
    else 
      if (is_callDereferenceCheck lid1) then
      match sts1 with
      |  Cons_list_sterm base 
        (Cons_list_sterm bound
        (Cons_list_sterm ptr Nil_list_sterm)) => 
          metadata_from_bep base bound ptr false accum
      | _ => accum
      end
    else accum)
end.

(* The propagation case
   sm: symbolic results of a subblock
   md: the bep we found so far
   accum: it must be md initially

   We consider 3 cases:
   1) b e p are copied
   2) b e are copied
   3) p is copied

   All the other cases are conservatively ignored.
*) 
Fixpoint metadata_from_sterms_aux (sm:smap) (accum md:beps) : beps :=
match md with
| nil => accum
| (b,e,p,im)::md' =>
    metadata_from_sterms_aux sm
      (match (lookupAL _ sm b, lookupAL _ sm e, lookupAL _ sm p) with
      | (Some sb, Some se, Some sp) =>
          metadata_from_bep sb se sp im accum
      | (Some sb, Some se, None) =>
          match (remove_cast sb, remove_cast se) with
          | (sterm_val (value_id b'), sterm_val (value_id e')) => 
              add_bep accum b' e' p im
          | _ => accum
          end
      | (None, None, Some sp) =>
          match (get_ptr_object sp) with
          | sterm_val (value_id p') => add_bep accum b e p' im
          | _ => accum
          end
      |  _ => accum
      end) md'
end.

Fixpoint metadata_from_sterms (sm:smap) (accum:beps) : beps :=
  metadata_from_sterms_aux sm accum accum.

(* For correctness it does not matter whether metadata_from_smem is called
 * before metadata_from_sterms. But hopefully callling metadata_from_smem 
 * first can reduce some steps towards fixpoint, because it adds more bep
 * for metadata_from_sterms to propagate.
 *)
Definition metadata_from_cmds (nbs2 : list nbranch) (accum:beps) : beps :=
let st2 := se_cmds sstate_init nbs2 in 
let accum' := metadata_from_smem st2.(SMem) accum in
metadata_from_sterms st2.(STerms) accum'.

(* Parameters at callsite are some other resources of metadata. If a function
   has a pointer input, the pointer also has its base/bound as additional 
   inputs.
*)

(* We assume that the orders of ars and sars are matched. The function finds
   the corresponding sterm to arg with id i. 

  define fid2 (ars2) { ... }

  define fid ... {
    ...
  l1:
    call fid2 sars2
  }  
*)
Fixpoint lookupSarg (ars2:list (typ*attributes*id)) 
  (sars2:list (typ*attributes*sterm)) (i:id) :option sterm :=
match (ars2, sars2) with
| (nil, nil) => None
| ((_,_,i')::ars2', (_,_,s')::sars2') =>
    if (eq_id i i') then Some s' else lookupSarg ars2' sars2' i
| _ => None
end.

(* ar_bep are base/bound in the arguments of function fid
   fid's arguments i args2
   sars2 is parameters supplied to fid at its callsite
*)
Fixpoint metadata_from_params (ar_bep:beps) ars2 sars2 
  (accum:beps) : beps :=
match ar_bep with
| nil => accum
| (b,e,p,im)::ar_bep' => metadata_from_params ar_bep' ars2 sars2 
    (match (lookupSarg ars2 sars2 b, lookupSarg ars2 sars2 e, 
      lookupSarg ars2 sars2 p) with
    | (Some sb, Some se, Some sp) => metadata_from_bep sb se sp im accum
    | _ => accum
    end)
end.

Definition get_arg_metadata (md:flnbeps) fid : beps :=
match lookupAL _ md fid with
| None => nil
| Some lnbeps => 
  match lookupAL _ lnbeps (l_of_arg tt) with
  | None => nil
  | Some nbeps => 
    match lookup_nbeps nbeps O with
    | None => nil
    | Some beps => beps
    end
  end
end.

Inductive sicall : Set :=
| stmn_icall_nptr : 
    id -> noret -> clattrs -> typ -> sterm -> 
      list (typ*attributes*sterm) -> sicall
| stmn_icall_ptr : 
    id -> noret -> clattrs -> typ -> sterm -> list (typ*attributes*sterm) ->
    id -> id -> id -> id -> id -> id -> id -> const -> const -> const -> sicall
.

Definition se_icall (st:sstate) (i:SBsyntax.call) : sicall :=
match i with
| SBsyntax.insn_call_nptr id0 nr ca t0 v0 p0 =>
    stmn_icall_nptr id0 nr ca t0 (value2Sterm st.(STerms) v0) 
      (list_param__list_typ_subst_sterm p0 st.(STerms))
| SBsyntax.insn_call_ptr id0 nr ca t0 v0 p0 sid id1 id2 id3 id4 id5 id6 
    cst0 cst1 cts2 =>
    stmn_icall_ptr id0 nr ca t0 (value2Sterm st.(STerms) v0) 
      (list_param__list_typ_subst_sterm p0 st.(STerms))
      sid id1 id2 id3 id4 id5 id6 cst0 cst1 cts2
end.

Definition metadata_from_iscall Ps2 (flnbep0:flnbeps) (accum:beps) (c2:sicall) 
  : beps :=
match c2 with
| stmn_icall_nptr _ _ _ _ t2 tsts2 =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (SBsyntax.lookupFdefViaIDFromProducts Ps2 fid2) with
        | None => accum
        | Some (SBsyntax.fdef_intro (fheader_intro _ _ _ args2 _) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        end
  | _ => accum
  end
| stmn_icall_ptr _ _ _ _ t2 tsts2 _ _ _ _ _ _ _ _ _ _ =>
  match remove_cast t2 with
  | sterm_val (value_const (const_gid _ fid2)) =>
      if (isCallLib fid2) then accum
      else
        match (SBsyntax.lookupFdefViaIDFromProducts Ps2 fid2) with
        | Some (SBsyntax.fdef_intro (fheader_intro _ _ _ (_::args2) _) _) =>
           metadata_from_params (get_arg_metadata flnbep0 fid2) args2 tsts2 accum
        | _ => accum
        end
  | _ => accum
  end
end.

Definition metadata_from_subblock Ps2 flnbep (sb2:SBsyntax.subblock)
  (accum:beps) : beps :=
match sb2 with
| SBsyntax.mkSB nbs2 call2 => 
  let st2 := se_cmds sstate_init nbs2 in 
  let cl2 := se_icall st2 call2 in
  let accum' := metadata_from_iscall Ps2 flnbep accum cl2 in
  let accum'' := metadata_from_sterms st2.(STerms) accum' in
  metadata_from_smem st2.(SMem) accum''
end.

(* Find beps not in cs2 *)
Fixpoint metadata_diff_cmds (md:beps) (cs2:cmds) : beps :=
match md with
| nil => md
| (b,e,p,im)::md' => 
    match lookupCmdViaIDFromCmds cs2 p with
    | Some _ => metadata_diff_cmds md' cs2
    | _ => (b,e,p,im)::metadata_diff_cmds md' cs2
    end
end.

Definition update_pred_subblock (accum:nbeps) nth bep : nbeps :=
 let bep_nth := 
   match lookup_nbeps accum (S nth) with
   | None => nil
   | Some bep_nth => bep_nth
   end in
 updateAdd_nbeps accum (S nth) (add_beps bep_nth bep).

(* The indices of subblocks are [1 .. len]. Subblocks are visited in a 
   reversed order. *)
Fixpoint metadata_from_subblocks_aux Ps2 flnbep len 
  (sbs2:list SBsyntax.subblock) (accum:nbeps) : nbeps :=
match sbs2 with
| nil => accum
| sb2::sbs2' => 
    let nth := List.length sbs2' in
    let bep :=
      match lookup_nbeps accum nth with
      | Some bep => bep 
      | None => nil
      end in
    let bep' := metadata_from_subblock Ps2 flnbep sb2 bep in
    let accum' := update_nbeps accum (len - nth) bep' in
    let accum'' := update_pred_subblock accum' nth 
      (metadata_diff_cmds bep' (nbranchs2cmds sb2.(SBsyntax.NBs))) in
    metadata_from_subblocks_aux Ps2 flnbep len sbs2' accum''
end.

Definition metadata_from_subblocks Ps2 flnbep (sbs2:list SBsyntax.subblock) 
  (accum:nbeps) : nbeps :=
metadata_from_subblocks_aux Ps2 flnbep (List.length sbs2) (List.rev sbs2) accum.

(* from phinodes 
    b = phi b1 b2 ...
    e = phi e1 e2 ...
    p = phi p1 p2 ...
  We only consider the case where all b e p are from phinodes. Because
  the phinodes of b e are generated by Softbound if their corresponding p
  is a phinode.
*)
Fixpoint lookupPhinode (phs:phinodes) (i:id) :=
match phs with
| nil => None
| (insn_phi i' t vs)::phs' =>
    if (eq_dec i i') then Some (insn_phi i' t vs)
    else lookupPhinode phs' i
end.

(* adding md0 into the last subblock of block l1 *)
Definition update_block_metadata (accum:lnbeps) (l1:l) (md0:beps) : lnbeps :=
let nbep :=
  match lookupAL _ accum l1 with
  | None => nil
  | Some nbep => nbep
  end in
let bep :=
  match lookup_nbeps nbep 0 with
  | None => nil
  | Some bep => bep
  end in
let bep' := add_beps bep md0 in
let nbep' := updateAdd_nbeps nbep 0 bep' in
updateAL _ accum l1 nbep'.

Definition metadata_from_value l1 (bv ev pv:value) im (accum:lnbeps) : lnbeps :=
match (bv, ev, pv) with
| (value_id bid, value_id eid, value_id pid) => 
    update_block_metadata accum l1 [(bid, eid, pid, im)]
| _ => accum
end.

Fixpoint metadata_from_list_value_l (bvls evls pvls:list_value_l) im 
  (accum:lnbeps) : lnbeps :=
match bvls with
| Nil_list_value_l => accum
| Cons_list_value_l bv bl bvls' =>
    metadata_from_list_value_l bvls' evls pvls im
      (match (getValueViaLabelFromValuels evls bl,
             getValueViaLabelFromValuels pvls bl) with
      | (Some ev, Some pv) => metadata_from_value bl bv ev pv im accum
      | _ => accum
      end)
end.

Fixpoint metadata_from_phinodes (ps2:phinodes) (accum:lnbeps) (md:beps) 
  : lnbeps :=
match md with
| nil => accum
| (b,e,p,im)::md' =>
    metadata_from_phinodes ps2
      (match (lookupPhinode ps2 b, lookupPhinode ps2 e, lookupPhinode ps2 p) with
       | (None, None, None) => accum
       | (Some (insn_phi _ _ bvls), 
          Some (insn_phi _ _ evls), 
          Some (insn_phi _ _ pvls)) =>
            metadata_from_list_value_l bvls evls pvls im accum 
       | _ => accum
       end) md'
end.

(* adding md0 into blocks ls *)
Fixpoint updatePredBlocks (ls:list l) (accum:lnbeps) (md0:beps) : lnbeps :=
match ls with
| nil => accum
| l1::ls' => updatePredBlocks ls' (update_block_metadata accum l1 md0) md0
end.

(* Find beps not in ps2 *)
Fixpoint metadata_diff_phinodes (md:beps) (ps2:phinodes) : beps :=
match md with
| nil => md
| (b,e,p,im)::md' => 
    match lookupPhinode ps2 b with
    | None => (b,e,p,im)::metadata_diff_phinodes md' ps2
    | _ => metadata_diff_phinodes md' ps2
    end
end.

(* The beps not in the current ps2 and cs2 are falled-through from
   previous blocks. 
Definition falling_through_metadata (md:beps) (b2:SBsyntax.block) : beps :=
match b2 with
| SBsyntax.block_common l2 ps2 cs2 tmn2 =>
    metadata_diff_cmds (metadata_diff_phinodes md ps2) cs2
end.
*)

(* Reimplement usedef, the one in infrastructure is WRONG!!!!!!!!!! *)
Definition usedef_block := list (l*list l).

Definition update_udb (udb:usedef_block) (lu ld:l) : usedef_block :=
let ls :=
  match lookupAL _ udb ld with
  | Some ls => ls
  | None => nil
  end in
match (in_dec l_dec lu ls) with
| left _ => udb
| right _ => updateAddAL _ udb ld (lu::ls) 
end.

Definition genBlockUseDef_block b (udb:usedef_block) : usedef_block :=
match b with
| SBsyntax.block_common l0 _ _ _ tmn2 =>
  match tmn2 with
  | insn_br _ _ l1 l2 => update_udb (update_udb udb l0 l2) l0 l1
  | insn_br_uncond _ l1 => update_udb udb l0 l1
  | _ => udb
  end
| _ => udb
end.

Fixpoint genBlockUseDef_blocks bs (udb:usedef_block) : usedef_block :=
match bs with
| nil => udb
| b::bs' => genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
end.

Definition genBlockUseDef_fdef f2 : usedef_block :=
match f2 with
| SBsyntax.fdef_intro _ lb2 => genBlockUseDef_blocks lb2 nil
end.

Definition metadata_from_block_aux Ps2 flnbep lnbep l2 ps2 sbs2 nbs2 udb :=
  let nbep0 :=
    match lookupAL _ lnbep l2 with
    | None => nil
    | Some nbep => nbep
    end in
  let bep0 :=
    match lookup_nbeps nbep0 0 with
    | None => nil
    | Some bep => bep
    end in
  let bep1 := metadata_from_cmds nbs2 bep0 in
  let nbep1 := updateAdd_nbeps nbep0 0 bep1 in
  let nbep2 := update_pred_subblock nbep1 0 
    (metadata_diff_cmds bep1 (nbranchs2cmds nbs2)) in
  let nbep3 := metadata_from_subblocks Ps2 flnbep sbs2 nbep2 in
  let lnbep' := updateAddAL _ lnbep l2 nbep3 in
  let bep_phi :=
    match lookup_nbeps nbep3 (List.length sbs2+1) with
    | None => nil
    | Some bep => bep
    end in
  let lnbep'' := metadata_from_phinodes ps2 lnbep' bep_phi in
  let preds := 
    match lookupAL _ udb l2 with
    | Some ls => ls
    | None => nil
    end in
  updatePredBlocks preds lnbep'' (metadata_diff_phinodes bep_phi ps2)
.

Definition metadata_from_block Ps2 flnbep (b2:SBsyntax.block) 
  (udb:usedef_block) (lnbep:lnbeps) : lnbeps :=
match b2 with
| SBsyntax.block_common l2 ps2 sbs2 nbs2 tmn2 =>
    metadata_from_block_aux Ps2 flnbep lnbep l2 ps2 sbs2 nbs2 udb
| SBsyntax.block_ret_ptr l2 ps2 sbs2 nbs2 
    (SBsyntax.insn_return_ptr _ _ _ _ _ vb _ _ ve _ vp _ _ _ _) =>
    let lnbep := metadata_from_value l2 vb ve vp true lnbep in 
    metadata_from_block_aux Ps2 flnbep lnbep l2 ps2 sbs2 nbs2 udb
end.

Fixpoint metadata_from_blocks_aux Ps2 flnbep (bs2:SBsyntax.blocks) 
  (udb:usedef_block) (lnbep:lnbeps) : lnbeps :=
match bs2 with
| nil => lnbep
| b2::bs2' => metadata_from_blocks_aux Ps2 flnbep bs2' udb 
    (metadata_from_block Ps2 flnbep b2 udb lnbep)
end.

Fixpoint eq_nbeps (md1 md2:nbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((n1,bep1)::md1', (n2,bep2)::md2') =>
    beq_nat n1 n2 && beq_nat (List.length bep1) (List.length bep2) &&
    eq_nbeps md1' md2'
| _ => false
end.

Fixpoint eq_lnbeps (md1 md2:lnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((l1,nbep1)::md1', (l2,nbep2)::md2') =>
    eq_l l1 l2 && eq_nbeps nbep1 nbep2 && eq_lnbeps md1' md2'
| _ => false
end.

Inductive onat :=
| Ozero : onat
| Osucc : onat -> onat.

Fixpoint metadata_from_blocks Ps2 flbep (bs2:SBsyntax.blocks) (udb:usedef_block) 
  (md:lnbeps) (bsteps:onat) : lnbeps :=
match bsteps with
| Ozero => md 
| Osucc bsteps' => 
  let md' := metadata_from_blocks_aux Ps2 flbep bs2 udb md in
  if eq_lnbeps md md' then md'
  else metadata_from_blocks Ps2 flbep bs2 udb md' bsteps'
end.

Fixpoint metadata_from_args (a:args) (md accum:beps) : beps :=
match md with
| nil => accum
| (b,e,p,im)::md' => 
    metadata_from_args a md'
      (match (lookupArgViaIDFromArgs a b,
              lookupArgViaIDFromArgs a e,
              lookupArgViaIDFromArgs a p) with
       | (Some _, Some _, Some _) => add_bep accum b e p im
       | _ => accum
       end)
end.

Definition metadata_from_fdef Ps2 flbep (f2:SBsyntax.fdef) (md:lnbeps) 
  (bsteps:onat) : lnbeps :=
match f2 with
| SBsyntax.fdef_intro ((fheader_intro _ t2 fid2 a2 _) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else 
   let accum := metadata_from_blocks Ps2 flbep lb2 
     (genBlockUseDef_fdef f2) md bsteps in 
      match SBsyntax.getEntryBlock f2 with
       | None => accum
       | Some (SBsyntax.block_common l2 _ _ _ _)
       | Some (SBsyntax.block_ret_ptr l2 _ _ _ _) =>
           match lookupAL _ accum l2 with
           | Some nbep => 
             match lookup_nbeps nbep (List.length nbep - 1) with
             | Some bep =>
               updateAddAL _ accum (l_of_arg tt) 
                 [(0, metadata_from_args a2 bep nil)]
             | None => accum
             end
           | _ => accum
           end
       end
end.

Fixpoint metadata_from_products_aux (Ps20 Ps2:SBsyntax.products) 
  (md:flnbeps) (bsteps:onat) : flnbeps :=
match Ps2 with
| nil => md
| SBsyntax.product_fdef f2::Ps2' => 
    let lnbep0 := match lookupAL _ md (SBsyntax.getFdefID f2) with
      | Some md => md 
      | None => nil
      end in 
    let lnbep := metadata_from_fdef Ps20 md f2 lnbep0 bsteps in
    let md' := updateAddAL _ md (SBsyntax.getFdefID f2) lnbep in
    metadata_from_products_aux Ps20 Ps2' md' bsteps
| _::Ps2' => metadata_from_products_aux Ps20 Ps2' md bsteps
end.

Fixpoint eq_flnbeps (md1 md2:flnbeps) : bool :=
match (md1, md2) with
| (nil, nil) => true
| ((f1,lnbeps1)::md1', (f2,lnbeps2)::md2') =>
    eq_id f1 f2 && eq_lnbeps lnbeps1 lnbeps2 && eq_flnbeps md1' md2'
| _ => false
end.

Fixpoint metadata_from_products (Ps2:SBsyntax.products) (md:flnbeps) 
  (bsteps:onat) (psteps:onat) : flnbeps :=
match psteps with
| Ozero => md 
| Osucc psteps' => 
  let md' := metadata_from_products_aux Ps2 Ps2 md bsteps in
  if eq_flnbeps md md' then md'
  else metadata_from_products Ps2 md' bsteps psteps'
end.

Definition metadata_from_module (m2:SBsyntax.module) (bsteps psteps:onat) :=
match m2 with
| SBsyntax.module_intro _ _ Ps2 => metadata_from_products Ps2 nil bsteps psteps
end.

(************************************************************)
(* Validating metadata *) 

Definition validate_metadata_from_blocks Ps2 flbep (bs2:SBsyntax.blocks) 
  (udb:usedef_block) (md:lnbeps) : bool :=
let md' := metadata_from_blocks_aux Ps2 flbep bs2 udb md in
eq_lnbeps md md'.

Fixpoint nbeps_to_beps (nbep:nbeps) (accum:beps) : beps :=
match nbep with
| nil => accum
| (_,bep)::nbep' => nbeps_to_beps nbep' bep++accum
end.

Fixpoint lnbeps_to_nbeps (lnbep:lnbeps) (accum:nbeps) : nbeps :=
match lnbep with
| nil => accum
| (_,nbep)::lnbep' => lnbeps_to_nbeps lnbep' nbep++accum
end.

Fixpoint in_beps (md:beps) (b e p:id) (im:bool): bool :=
match md with
| nil => false
| (b',e',p',im')::md' => 
    if (eq_id b b' && eq_id e e' && eq_id p p' && eqb im im') then true
    else in_beps md' b e p im
end.

Fixpoint disjoint_mptr_fptr_metadata_aux (bep:beps) : bool :=
match bep with
| nil => true
| (b,e,p,im)::bep' => (negb (in_beps bep' b e p (negb im))) && 
    disjoint_mptr_fptr_metadata_aux bep'
end.

Definition disjoint_mptr_fptr_metadata (md:lnbeps) : bool :=
disjoint_mptr_fptr_metadata_aux (nbeps_to_beps (lnbeps_to_nbeps md nil) nil).

Definition validate_metadata_from_fdef Ps2 flbep (f2:SBsyntax.fdef) (md:lnbeps) 
  : bool :=
match f2 with
| SBsyntax.fdef_intro ((fheader_intro _ t2 fid2 a2 _) as fh2) lb2 =>
  if (isCallLib fid2) then true
  else 
    disjoint_mptr_fptr_metadata md &&
    validate_metadata_from_blocks Ps2 flbep lb2 (genBlockUseDef_fdef f2) md &&
    match SBsyntax.getEntryBlock f2 with
    | None => false
    | Some (SBsyntax.block_common l2 _ _ _ _)
    | Some (SBsyntax.block_ret_ptr l2 _ _ _ _) =>
        match lookupAL _ md l2 with
        | Some nbep => 
          match lookup_nbeps nbep (List.length nbep - 1) with
          | Some bep =>
             match lookupAL _ md (l_of_arg tt) with
             | None => false
             | Some nbep' => 
                eq_nbeps nbep' [(0, metadata_from_args a2 bep nil)]
             end
          | None => false
          end
        | _ => false
        end
    end
end.

Fixpoint validate_metadata_from_products_aux (Ps20 Ps2:SBsyntax.products) 
  (md:flnbeps) : bool :=
match Ps2 with
| nil => true
| SBsyntax.product_fdef f2::Ps2' => 
    match lookupAL _ md (SBsyntax.getFdefID f2) with
    | Some lnbep =>
        validate_metadata_from_fdef Ps20 md f2 lnbep &&
        validate_metadata_from_products_aux Ps20 Ps2' md
    | None => false
    end
| _::Ps2' => validate_metadata_from_products_aux Ps20 Ps2' md
end.

Definition validate_metadata_from_module (m2:SBsyntax.module) (md:flnbeps) 
  : bool :=
match m2 with
| SBsyntax.module_intro _ _ Ps2 => validate_metadata_from_products_aux Ps2 Ps2 md
end.

(************************************************************)
(* Generating addrof base/bound *) 

Definition abes := list (id*id).

(* add addrof b e if they are not in *)
Fixpoint add_abes (md:abes) (ab ae:id) : abes :=
match md with
| nil => [(ab,ae)]
| (ab',ae')::md' => 
    if (eq_id ab ab' && eq_id ae ae') then md
    else (ab',ae')::add_abes md' ab ae
end.

Fixpoint addrofbe_from_smem (sm:smem) (accum:abes) : abes :=
match sm with
| smem_init => accum
| smem_malloc sm1 _ _ _
| smem_alloca sm1 _ _ _
| smem_free sm1 _ _
| smem_load sm1 _ _ _ 
| smem_store sm1 _ _ _ _ => addrofbe_from_smem sm1 accum
| smem_lib sm1 lid1 sts1 =>
    addrofbe_from_smem sm1
    (if (is_hashLoadBaseBound lid1) then
      match sts1 with
      |  Cons_list_sterm _ 
        (Cons_list_sterm addr_of_base
        (Cons_list_sterm addr_of_bound
        (Cons_list_sterm _
        (Cons_list_sterm _
        (Cons_list_sterm _ Nil_list_sterm))))) =>
          match (addr_of_base, addr_of_bound) with
          | (sterm_val (value_id ab), sterm_val (value_id ae)) =>
              add_abes accum ab ae
          | _ => accum
          end
      | _ => accum
      end
    else accum)
end.
 
Definition addrofbe_from_cmds (nbs2 : list nbranch) (md:abes) : abes :=
let st2 := se_cmds sstate_init nbs2 in 
addrofbe_from_smem st2.(SMem) md.

Definition addrofbe_from_subblock (sb2:SBsyntax.subblock) (md:abes) : abes :=
match sb2 with
| SBsyntax.mkSB nbs2 _ => addrofbe_from_cmds nbs2 md
end.

Fixpoint addrofbe_from_subblocks (sbs2:list SBsyntax.subblock) (md:abes) 
  : abes :=
match sbs2 with
| nil => md
| sb2::sbs2' => addrofbe_from_subblocks sbs2' (addrofbe_from_subblock sb2 md)
end.

Definition addrofbe_from_block (b2:SBsyntax.block) (md:abes) : abes :=
match b2 with
| SBsyntax.block_common l2 ps2 sbs2 nbs2 _ 
| SBsyntax.block_ret_ptr l2 ps2 sbs2 nbs2 _ =>
  let accum1 := addrofbe_from_cmds nbs2 md in
  addrofbe_from_subblocks sbs2 accum1
end.

Fixpoint addrofbe_from_blocks (bs2:SBsyntax.blocks) (md:abes) : abes :=
match bs2 with
| nil => md
| b2::bs2' => addrofbe_from_blocks bs2' (addrofbe_from_block b2 md)
end.

Definition addrofbe_from_fdef (f2:SBsyntax.fdef) (md:abes) : abes :=
match f2 with
| SBsyntax.fdef_intro ((fheader_intro _ t2 fid2 a2 _) as fh2) lb2 =>
  if (isCallLib fid2) then md 
  else addrofbe_from_blocks lb2 nil
end.

Definition fabes := list (id*abes).

Fixpoint addrofbe_from_products (Ps2:SBsyntax.products) (md:fabes) : fabes :=
match Ps2 with
| nil => md
| SBsyntax.product_fdef f2::Ps2' => 
    let abes := addrofbe_from_fdef f2 nil in
    let md' := updateAddAL _ md (SBsyntax.getFdefID f2) abes in
    addrofbe_from_products Ps2' md'
| _::Ps2' => addrofbe_from_products Ps2' md
end.

Definition addrofbe_from_module (m2:SBsyntax.module) :=
match m2 with
| SBsyntax.module_intro _ _ Ps2 => addrofbe_from_products Ps2 nil
end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
