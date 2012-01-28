Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import dtree.
Require Import primitives.
Require Import Maps.

Record vmap := mkVMap {
  alloca: value;
  others: AssocList value
}.

Definition vm_subst_cmd (vm:vmap) (c:cmd) := 
List.fold_right 
  (fun elt c' => let '(id0, v0) := elt in subst_cmd id0 v0 c') 
  c vm.(others).

Definition vm_subst_tmn (vm:vmap) (tmn:terminator) := 
List.fold_right 
  (fun elt tmn' => let '(id0, v0) := elt in subst_tmn id0 v0 tmn') 
  tmn vm.(others).

Definition vm_subst_phi (vm:vmap) (pn:phinode) := 
List.fold_right 
  (fun elt pn' => let '(id0, v0) := elt in subst_phi id0 v0 pn') 
  pn vm.(others).

Definition vm_get_alloca (vm:vmap): value := vm.(alloca).

Definition vm_set_others (vm:vmap) id0 v0: vmap :=
mkVMap vm.(alloca) (ATree.set id0 v0 vm.(others)).

Definition vm_set_alloca (vm:vmap) v0: vmap :=
mkVMap v0 vm.(others).

Definition ssa_renaming_cmd (c:cmd) (pid:id) (vm: vmap): option cmd * vmap :=
let c' := vm_subst_cmd vm c in 
match c' with
| insn_load id0 _ (value_id qid) _ => 
    if (id_dec pid qid) then (None, vm_set_others vm id0 (vm_get_alloca vm))
    else (Some c', vm)
| insn_store _ _ v0 (value_id qid) _ => 
    if (id_dec pid qid) then (None, vm_set_alloca vm v0) 
    else (Some c', vm)
| _ => (Some c', vm)
end.

Fixpoint ssa_renaming_cmds (cs:cmds) (pid:id) (vm: vmap) : cmds * vmap :=
match cs with
| nil => (nil, vm)
| c :: cs' =>
    let '(optc0, vm0) := ssa_renaming_cmd c pid vm in
    let '(cs1, vm1) := ssa_renaming_cmds cs' pid vm0 in
    (match optc0 with 
     | Some c0 => c0::cs1
     | None => cs1
     end, vm1)
end.

Definition vm_subst_value (vm:vmap) (v:value) := 
List.fold_right 
  (fun elt v' => let '(id0, v0) := elt in subst_value id0 v0 v') 
  v vm.(others).

Fixpoint ssa_renaming_phis_operands (l0:l) (ps:phinodes) (pid:id) 
  (newpids:list id) (vm: vmap) : phinodes :=
match ps with
| nil => nil
| insn_phi id0 t0 vls :: ps' =>
    (if (id_dec id0 pid) || (in_dec id_dec id0 newpids) then
      insn_phi id0 t0 
        (make_list_value_l
          (map_list_value_l
            (fun v1 l1 => 
               (if (l_dec l0 l1) 
                then vm_get_alloca vm
                else v1, l1)) vls))
    else insn_phi id0 t0 
        (make_list_value_l
          (map_list_value_l
            (fun v1 l1 => 
               (if (l_dec l0 l1) 
                then vm_subst_value vm v1
                else v1, l1)) vls)))::
    ssa_renaming_phis_operands l0 ps' pid newpids vm
end.

Definition block_subst (f:fdef) (l0:l) (b0:block) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh 
  (List.map (fun b =>      
             let '(block_intro l1 _ _ _) := b in
             if (l_dec l1 l0) then b0 else b) bs).

Definition ssa_renaming_succ_phis (f:fdef) (lcur:l) (succ:list l) (pid:id) 
  (newpids:list id) (vm:vmap): fdef :=
List.fold_left 
  (fun acc lnext =>
   match lookupBlockViaLabelFromFdef acc lnext with
   | None => acc
   | Some (block_intro _ ps cs tmn) =>
       let ps':= ssa_renaming_phis_operands lcur ps pid newpids vm in
       block_subst acc lnext (block_intro lnext ps' cs tmn)
   end) succ f.

Fixpoint update_vm_by_phis (ps:phinodes) (pid:id) (newpids:list id)
  (vm: vmap) : vmap :=
match ps with
| nil => vm
| insn_phi id0 t0 vls :: ps' =>
    if (in_dec id_dec id0 newpids) then vm_set_alloca vm (value_id id0)
    else update_vm_by_phis ps' pid newpids vm
end.

Fixpoint ssa_renaming_dtree (f:fdef) (dt: DTree) (pid:id) (newpids:list id) 
  (vm:vmap) : fdef :=
match dt with
| DT_node l0 dts => 
    match lookupBlockViaLabelFromFdef f l0 with
    | None => f
    | Some (block_intro l0 ps cs tmn) =>
        let ps' := List.map (vm_subst_phi vm) ps in
        let vm1 := update_vm_by_phis ps pid newpids vm in
        let '(cs', vm2) := ssa_renaming_cmds cs pid vm1 in
        let tmn' := vm_subst_tmn vm2 tmn in
        let f2 := block_subst f l0 (block_intro l0 ps' cs' tmn') in
        let f3 :=
          ssa_renaming_succ_phis f2 l0 
            (successors_terminator tmn) pid newpids vm2 in
        ssa_renaming_dtrees f3 dts pid newpids vm2
    end
end
with ssa_renaming_dtrees (f:fdef) (dts: DTrees) (pid:id)(newpids:list id) 
  (vm:vmap) : fdef :=
match dts with
| DT_nil => f
| DT_cons dt dts' => 
    let f' := ssa_renaming_dtree f dt pid newpids vm in
    ssa_renaming_dtrees f' dts' pid newpids vm
end.

Definition vm_init (ty:typ) :=
  mkVMap (value_const (const_undef ty)) (ATree.empty value).

Definition ssa_renaming (f:fdef) (dt:DTree) (pid:id) (ty:typ) 
  (newpids:list id) : fdef:= 
let f1 := ssa_renaming_dtree f dt pid newpids (vm_init ty) in
if used_in_fdef pid f1 then f1 else remove_fdef pid f1.

Definition insert_phis (f:fdef) (rd:list l) (pid:id) (ty:typ): fdef * list id :=
let preds := make_predecessors (successors f) in
let '(fdef_intro fh bs) := f in
let ex_ids := getFdefLocs f in
let '(bs', _, newpids) :=
  (List.fold_left
    (fun acc b =>
       let '(bs', ex_ids', newpids) := acc in
       let '(block_intro l0 ps cs tmn) := b in
       match ATree.get l0 preds with
       | Some ((_ :: _) as pds) => 
           let '(exist pid' _) := AtomImpl.atom_fresh_for_list ex_ids' in
           (block_intro l0 
             (insn_phi pid' ty 
               (fold_left 
                  (fun acc p => 
                     Cons_list_value_l 
                       (if In_dec l_dec p rd then value_id pid 
                       else value_const (const_undef ty)) p acc) 
                   pds Nil_list_value_l)::ps) 
             cs tmn::bs', pid'::ex_ids', pid'::newpids)
       | _ => (b::bs', ex_ids', newpids)
       end) (List.rev bs) (nil, ex_ids, nil)) in
(fdef_intro fh bs', newpids).

Definition is_promotable (f:fdef) (pid:id) : bool :=
let '(fdef_intro _ bs) := f in
fold_left 
  (fun acc b => 
     let '(block_intro _ ps cs tmn) := b in
     if (List.fold_left (fun re p => re || used_in_phi pid p) ps 
          (used_in_tmn pid tmn)) then false
     else
       fold_left 
         (fun acc0 c =>
          if used_in_cmd pid c then
            match c with
            | insn_load _ _ _ _ => acc0
            | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
            | _ => false
            end
          else acc0) cs acc
  ) bs true. 

Fixpoint find_promotable_alloca (f:fdef) (cs:cmds) (dones:list id) 
  : option (id * typ * align) :=
match cs with
| nil => None
| insn_alloca pid ty _ al :: cs' =>
    if is_promotable f pid && negb (In_dec id_dec pid dones) 
    then Some (pid, ty, al)
    else find_promotable_alloca f cs' dones
| _ :: cs' => find_promotable_alloca f cs' dones
end.

Definition mem2reg_fdef_iter (f:fdef) (dt:DTree) (rd:list l) (dones:list id)
  : fdef * bool * list id := 
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    match find_promotable_alloca f cs dones with
    | None => (f, false, dones)
    | Some (pid, ty, al) => 
        let '(f', newpids) := insert_phis f rd pid ty in
        (ssa_renaming f' dt pid ty newpids, true, pid::dones)
    end
| _ => (f, false, dones)
end.

Definition gen_fresh_ids (rd:list id) (ex_ids:list atom)
  : (ATree.t (id * id * id) * list atom) :=
  List.fold_left 
    (fun acc l0 => 
       let '(nids', ex_ids') := acc in
       let '(exist lid' _) := AtomImpl.atom_fresh_for_list ex_ids' in
       let '(exist pid' _) := AtomImpl.atom_fresh_for_list (lid'::ex_ids') in
       let '(exist sid' _) := 
         AtomImpl.atom_fresh_for_list (pid'::lid'::ex_ids') in
       (ATree.set l0 (lid', pid', sid') nids', sid'::pid'::lid'::ex_ids')
    ) rd (ATree.empty (id * id * id), ex_ids).

Definition gen_phinode (pid':id) (ty:typ) (nids:ATree.t (id*id*id)) (pds:list l) 
  : phinode :=
  insn_phi pid' ty 
    (fold_left 
       (fun acc p => 
          Cons_list_value_l 
            (match ATree.get p nids with
             | Some (lid0, _, _) => value_id lid0
             | None => value_const (const_undef ty)
             end) 
             p acc) 
        pds Nil_list_value_l).

Definition phinodes_placement_block (pid:id) (ty:typ) (al:align) 
  (nids:ATree.t (id*id*id)) (succs preds:ATree.t (list l)) (b:block) : block :=
   let '(block_intro l0 ps cs tmn) := b in 
   match ATree.get l0 nids with
   | Some (lid, pid', sid) =>
     let cs' := 
       match ATree.get l0 succs with
       | Some (_::_) => [insn_load lid ty (value_id pid) al]
       | _ => nil
       end in
     match ATree.get l0 preds with
     | Some ((_ :: _) as pds) => 
         block_intro l0
           ((gen_phinode pid' ty nids pds)::ps)
           (insn_store sid ty (value_id pid') (value_id pid) al::
            cs ++ cs') tmn
     | _ => block_intro l0 ps (cs ++ cs') tmn
     end
  | _ => b
  end.

Definition phinodes_placement_blocks (bs:blocks) (pid:id) (ty:typ) (al:align) 
  (nids:ATree.t (id*id*id)) (succs preds:ATree.t (list l)) : blocks :=
List.map (phinodes_placement_block pid ty al nids succs preds) bs.
(*
List.fold_left
  (fun bs' b => phinodes_placement_block b pid ty al nids succs preds :: bs') 
  (List.rev bs) nil.
*)

Definition phinodes_placement (f:fdef) (rd:list l) (pid:id) (ty:typ) (al:align) 
  (succs preds:ATree.t (list l)) : fdef :=
let '(fdef_intro fh bs) := f in
let '(nids, _) := gen_fresh_ids rd (getFdefLocs f) in
let bs1 := phinodes_placement_blocks bs pid ty al nids succs preds in
fdef_intro fh bs1.

Fixpoint find_init_stld (cs:cmds) (pid:id) (dones:list id) 
  : option (id * value * cmds + value * cmds) :=
match cs with
| nil => None
| insn_store sid _ v0 (value_id qid) _ :: cs' =>
    if (in_dec id_dec sid dones) then find_init_stld cs' pid dones
    else
      if (id_dec pid qid) then Some (inl (sid, v0, cs'))
      else find_init_stld cs' pid dones
| insn_alloca qid ty _ _ :: cs' =>
    if (in_dec id_dec qid dones) then find_init_stld cs' pid dones
    else
      if (id_dec pid qid) then 
        Some (inr (value_const (const_undef ty), cs'))
      else find_init_stld cs' pid dones
| _ :: cs' => find_init_stld cs' pid dones
end.

Fixpoint find_next_stld (cs:cmds) (pid:id) : option (id + id * value) :=
match cs with
| nil => None
| insn_store sid _ v0 (value_id qid) _ :: cs' =>
    if (id_dec pid qid) then Some (inr (sid, v0))
    else find_next_stld cs' pid
| insn_load lid _ (value_id qid) _ :: cs' =>
    if (id_dec pid qid) then Some (inl lid)
    else find_next_stld cs' pid
| _ :: cs' => find_next_stld cs' pid
end.

Definition elim_stld_cmds (f:fdef) (cs:cmds) (pid:id) (dones:list id) 
  : fdef * bool * list id :=
match find_init_stld cs pid dones with
| None => (f, false, dones)
| Some (inl (sid1, v1, cs')) =>
    match find_next_stld cs' pid with
    | None => (f, true, sid1::dones)
    | Some (inl lid) => (remove_fdef lid (subst_fdef lid v1 f), true, dones)
    | Some (inr (sid2, v2)) => (remove_fdef sid1 f, true, dones)
    end
| Some (inr (v1, cs')) =>
    match find_next_stld cs' pid with
    | None => (f, true, pid::dones)
    | Some (inl lid) => (remove_fdef lid (subst_fdef lid v1 f), true, dones)
    | Some (inr (sid2, v2)) => (f, true, pid::dones)
    end
end.

Fixpoint elim_stld_blocks (f:fdef) (bs: blocks) (pid:id) (dones:list id) 
  : fdef * bool * list id :=
match bs with
| nil => (f, false, dones)
| block_intro _ _ cs _::bs' =>
    let '(f', changed, dones') := elim_stld_cmds f cs pid dones in
    if changed then (f', true, dones') else elim_stld_blocks f' bs' pid dones
end.

Definition elim_stld_fdef (f:fdef) (pid:id) (dones:list id) 
  : fdef * bool * list id :=
let '(fdef_intro fh bs) := f in elim_stld_blocks f bs pid dones.

Definition elim_stld_step (pid:id) (st: fdef * list id) 
  : fdef * list id + fdef * list id :=
let '(f, dones) := st in
let '(f1, changed1, dones1) := elim_stld_fdef f pid dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

Parameter does_stld_elim : unit -> bool.

Definition load_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_load _ _ v _ => used_in_value id' v
| _ => false
end.

Definition load_in_block (id':id) (b:block) : bool := 
match b with
| block_intro _ _ cs0 _ =>
  (List.fold_left (fun re c => re || load_in_cmd id' c) cs0 false)
end.

Definition load_in_fdef (id':id) (f:fdef) : bool := 
match f with
| fdef_intro _ bs => 
  List.fold_left (fun re b => re || load_in_block id' b) bs false
end.

Fixpoint elim_dead_st_cmds (cs:cmds) (pid:id) : cmds :=
match cs with
| nil => nil
| insn_store sid _ _ (value_id qid) _ as c :: cs' =>
    if (id_dec pid qid) then elim_dead_st_cmds cs' pid
    else c :: elim_dead_st_cmds cs' pid
| c::cs' => c :: elim_dead_st_cmds cs' pid
end.

Definition elim_dead_st_block (pid:id) (b: block) : block :=
match b with
| block_intro l0 ps cs tmn => block_intro l0 ps (elim_dead_st_cmds cs pid) tmn
end.

Definition elim_dead_st_fdef (f:fdef) (pid:id) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map (elim_dead_st_block pid) bs).

Definition macro_mem2reg_fdef_iter (f:fdef) (rd:list l) (succs preds:ATree.t (list l)) 
  (dones:list id) : fdef * bool * list id := 
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    match find_promotable_alloca f cs dones with
    | None => (f, false, dones)
    | Some (pid, ty, al) => 
        let f1 := phinodes_placement f rd pid ty al succs preds in
        let '(f2, _) := 
          if does_stld_elim tt then
            SafePrimIter.iterate _ (elim_stld_step pid) (f1, nil) 
          else (f1, nil)
        in
        let f3 :=
          if load_in_fdef pid f2 then f2 else elim_dead_st_fdef f2 pid
        in
        (if used_in_fdef pid f3 then f3 else remove_fdef pid f3,
         true, pid::dones)
    end
| _ => (f, false, dones)
end.

Definition macro_mem2reg_fdef_step (rd:list l) (succs preds:ATree.t (list l)) 
  (st:fdef * list id) : (fdef * list id) + (fdef * list id) :=
let '(f, dones) := st in
let '(f1, changed1, dones1) := 
      macro_mem2reg_fdef_iter f rd succs preds dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

Definition mem2reg_fdef_step (dt:DTree) (rd:list l) (st:fdef * list id) 
  : (fdef * list id) + (fdef * list id) :=
let '(f, dones) := st in
let '(f1, changed1, dones1) := mem2reg_fdef_iter f dt rd dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

Fixpoint remove_redundancy (acc:ids) (ids0:ids) : ids :=
match ids0 with
| nil => acc
| id1::ids0' => 
    if (In_dec id_dec id1 acc) then remove_redundancy acc ids0'
    else remove_redundancy (id1::acc) ids0'
end.

Definition eliminate_phi (f:fdef) (pn:phinode): fdef * bool:=
let '(insn_phi pid _ vls) := pn in 
let vls' := unmake_list_value_l vls in
let ops := values2ids (list_prj1 _ _ vls') in
if (beq_nat (List.length ops) (List.length vls')) then
  let ids0 := pid :: ops in
  let ndp0 := remove_redundancy nil ids0 in
  match ndp0 with
  | id1::id2::nil =>
    let pid := getPhiNodeID pn in
    if (id_dec pid id1) then 
      (remove_fdef pid (isubst_fdef pid id2 f), true)
    else if (id_dec pid id2) then 
      (remove_fdef pid (isubst_fdef pid id1 f), true)
    else (f, false)
  | id1::nil => (remove_fdef id1 f, false)
  | _ => (f, false)
  end
else (f, false).

Fixpoint eliminate_phis (f:fdef) (ps: phinodes): fdef * bool :=
match ps with
| nil => (f, false)
| p::ps' =>
    let '(f', changed) := eliminate_phi f p in
    if changed then (f', true) else eliminate_phis f' ps' 
end.

Fixpoint eliminate_blocks (f:fdef) (bs: blocks): fdef * bool :=
match bs with
| nil => (f, false)
| block_intro _ ps _ _::bs' =>
    let '(f', changed) := eliminate_phis f ps in
    if changed then (f', true) else eliminate_blocks f' bs' 
end.

Definition eliminate_fdef (f:fdef) : fdef * bool :=
let '(fdef_intro fh bs) := f in eliminate_blocks f bs.

Definition eliminate_step (f: fdef) : fdef + fdef :=
let '(f1, changed1) := eliminate_fdef f  in
if changed1 then inr _ f1 else inl _ f1.

Parameter does_phi_elim : unit -> bool.
Parameter does_macro_m2r : unit -> bool.

Definition mem2reg_fdef (f:fdef) : fdef :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ cs _), Some rd =>
  if print_reachablity rd then
    let '(f1, _) := 
      if (does_macro_m2r tt) then
        let succs := successors f in
        let preds := make_predecessors succs in
        SafePrimIter.iterate _ 
          (macro_mem2reg_fdef_step rd succs preds) (f, nil) 
      else
        let b := bound_fdef f in
        let dts := dom_analyze f in
        let chains := compute_sdom_chains b dts rd in
        let dt :=
          fold_left 
            (fun acc elt => 
             let '(_, chain):=elt in 
             create_dtree_from_chain acc chain) 
            chains (DT_node root DT_nil) in
        if print_dominators b dts && print_dtree dt then
           SafePrimIter.iterate _ (mem2reg_fdef_step dt rd) (f, nil) 
        else (f, nil)
    in
    let f2 :=
      if does_phi_elim tt then SafePrimIter.iterate _ eliminate_step f1
      else f1 in
    match fix_temporary_fdef f2 with
    | Some f' => f'
    | None => f
    end
  else f
| _, _ => f
end.

Definition run (m:module) : module :=
let '(module_intro los nts ps) := m in
module_intro los nts 
  (List.map (fun p =>
             match p with
             | product_fdef f => product_fdef (mem2reg_fdef f)
             | _ => p
             end) ps).

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
