open Coqlib
open Datatypes
open EqNat
open Iteration
open Kildall
open List0
open Maps
open Metatheory
open MetatheoryAtom
open Alist
open Analysis
open Dtree
open Infrastructure
open Primitives
open Syntax

type vmap = { alloca : LLVMsyntax.value;
              others : LLVMsyntax.value coq_AssocList }

(** val vmap_rect :
    (LLVMsyntax.value -> LLVMsyntax.value coq_AssocList -> 'a1) -> vmap ->
    'a1 **)

let vmap_rect f v =
  let { alloca = x; others = x0 } = v in f x x0

(** val vmap_rec :
    (LLVMsyntax.value -> LLVMsyntax.value coq_AssocList -> 'a1) -> vmap ->
    'a1 **)

let vmap_rec f v =
  let { alloca = x; others = x0 } = v in f x x0

(** val alloca : vmap -> LLVMsyntax.value **)

let alloca x = x.alloca

(** val others : vmap -> LLVMsyntax.value coq_AssocList **)

let others x = x.others

(** val vm_subst_cmd : vmap -> LLVMsyntax.cmd -> LLVMsyntax.cmd **)

let vm_subst_cmd vm c =
  fold_right (fun elt c' -> let id0,v0 = elt in subst_cmd id0 v0 c') c
    vm.others

(** val vm_subst_tmn :
    vmap -> LLVMsyntax.terminator -> LLVMsyntax.terminator **)

let vm_subst_tmn vm tmn =
  fold_right (fun elt tmn' -> let id0,v0 = elt in subst_tmn id0 v0 tmn') tmn
    vm.others

(** val vm_subst_phi : vmap -> LLVMsyntax.phinode -> LLVMsyntax.phinode **)

let vm_subst_phi vm pn =
  fold_right (fun elt pn' -> let id0,v0 = elt in subst_phi id0 v0 pn') pn
    vm.others

(** val vm_get_alloca : vmap -> LLVMsyntax.value **)

let vm_get_alloca vm =
  vm.alloca

(** val vm_set_others : vmap -> AtomImpl.atom -> LLVMsyntax.value -> vmap **)

let vm_set_others vm id0 v0 =
  { alloca = vm.alloca; others = (ATree.set id0 v0 vm.others) }

(** val vm_set_alloca : vmap -> LLVMsyntax.value -> vmap **)

let vm_set_alloca vm v0 =
  { alloca = v0; others = vm.others }

(** val ssa_renaming_cmd :
    LLVMsyntax.cmd -> LLVMsyntax.id -> vmap -> LLVMsyntax.cmd option*vmap **)

let ssa_renaming_cmd c pid vm =
  let c' = vm_subst_cmd vm c in
  (match c' with
     | LLVMsyntax.Coq_insn_load (id0, t0, v, a) ->
         (match v with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then None,(vm_set_others vm id0 (vm_get_alloca vm))
                else (Some c'),vm
            | LLVMsyntax.Coq_value_const c0 -> (Some c'),vm)
     | LLVMsyntax.Coq_insn_store (i, t0, v0, v, a) ->
         (match v with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then None,(vm_set_alloca vm v0)
                else (Some c'),vm
            | LLVMsyntax.Coq_value_const c0 -> (Some c'),vm)
     | _ -> (Some c'),vm)

(** val ssa_renaming_cmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> vmap -> LLVMsyntax.cmds*vmap **)

let rec ssa_renaming_cmds cs pid vm =
  match cs with
    | [] -> [],vm
    | c::cs' ->
        let optc0,vm0 = ssa_renaming_cmd c pid vm in
        let cs1,vm1 = ssa_renaming_cmds cs' pid vm0 in
        (match optc0 with
           | Some c0 -> c0::cs1
           | None -> cs1),vm1

(** val vm_subst_value : vmap -> LLVMsyntax.value -> LLVMsyntax.value **)

let vm_subst_value vm v =
  fold_right (fun elt v' -> let id0,v0 = elt in subst_value id0 v0 v') v
    vm.others

(** val ssa_renaming_phis_operands :
    LLVMsyntax.l -> LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id
    list -> vmap -> LLVMsyntax.phinodes **)

let rec ssa_renaming_phis_operands l0 ps pid newpids vm =
  match ps with
    | [] -> []
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, vls) = p in
        (if if proj_sumbool (LLVMinfra.id_dec id0 pid)
            then true
            else proj_sumbool (in_dec LLVMinfra.id_dec id0 newpids)
         then LLVMsyntax.Coq_insn_phi (id0, t0,
                (LLVMsyntax.make_list_value_l
                  (LLVMsyntax.map_list_value_l (fun v1 l1 ->
                    (if LLVMinfra.l_dec l0 l1 then vm_get_alloca vm else v1),l1)
                    vls)))
         else LLVMsyntax.Coq_insn_phi (id0, t0,
                (LLVMsyntax.make_list_value_l
                  (LLVMsyntax.map_list_value_l (fun v1 l1 ->
                    (if LLVMinfra.l_dec l0 l1
                     then vm_subst_value vm v1
                     else v1),l1) vls))))::(ssa_renaming_phis_operands l0 ps'
                                             pid newpids vm)

(** val block_subst :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block -> LLVMsyntax.fdef **)

let block_subst f l0 b0 =
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  LLVMsyntax.Coq_fdef_intro (fh,
  (map (fun b ->
    let LLVMsyntax.Coq_block_intro (l1, p, c, t0) = b in
    if LLVMinfra.l_dec l1 l0 then b0 else b) bs))

(** val ssa_renaming_succ_phis :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l list -> LLVMsyntax.id ->
    LLVMsyntax.id list -> vmap -> LLVMsyntax.fdef **)

let ssa_renaming_succ_phis f lcur succ pid newpids vm =
  fold_left (fun acc lnext ->
    match LLVMinfra.lookupBlockViaLabelFromFdef acc lnext with
      | Some b ->
          let LLVMsyntax.Coq_block_intro (l0, ps, cs, tmn) = b in
          let ps' = ssa_renaming_phis_operands lcur ps pid newpids vm in
          block_subst acc lnext (LLVMsyntax.Coq_block_intro (lnext, ps', cs,
            tmn))
      | None -> acc) succ f

(** val update_vm_by_phis :
    LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.id list -> vmap ->
    vmap **)

let rec update_vm_by_phis ps pid newpids vm =
  match ps with
    | [] -> vm
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, vls) = p in
        if in_dec LLVMinfra.id_dec id0 newpids
        then vm_set_alloca vm (LLVMsyntax.Coq_value_id id0)
        else update_vm_by_phis ps' pid newpids vm

(** val ssa_renaming_dtree :
    LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.id -> LLVMsyntax.id list ->
    vmap -> LLVMsyntax.fdef **)

let rec ssa_renaming_dtree f dt pid newpids vm =
  let DT_node (l0, dts) = dt in
  (match LLVMinfra.lookupBlockViaLabelFromFdef f l0 with
     | Some b ->
         let LLVMsyntax.Coq_block_intro (l1, ps, cs, tmn) = b in
         let ps' = map (vm_subst_phi vm) ps in
         let vm1 = update_vm_by_phis ps pid newpids vm in
         let cs',vm2 = ssa_renaming_cmds cs pid vm1 in
         let tmn' = vm_subst_tmn vm2 tmn in
         let f2 =
           block_subst f l1 (LLVMsyntax.Coq_block_intro (l1, ps', cs', tmn'))
         in
         let f3 =
           ssa_renaming_succ_phis f2 l1 (LLVMinfra.successors_terminator tmn)
             pid newpids vm2
         in
         ssa_renaming_dtrees f3 dts pid newpids vm2
     | None -> f)

(** val ssa_renaming_dtrees :
    LLVMsyntax.fdef -> coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.id list ->
    vmap -> LLVMsyntax.fdef **)

and ssa_renaming_dtrees f dts pid newpids vm =
  match dts with
    | DT_nil -> f
    | DT_cons (dt, dts') ->
        let f' = ssa_renaming_dtree f dt pid newpids vm in
        ssa_renaming_dtrees f' dts' pid newpids vm

(** val vm_init : LLVMsyntax.typ -> vmap **)

let vm_init ty =
  { alloca = (LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_undef ty));
    others = ATree.empty }

(** val ssa_renaming :
    LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.id -> LLVMsyntax.typ ->
    LLVMsyntax.id list -> LLVMsyntax.fdef **)

let ssa_renaming f dt pid ty newpids =
  let f1 = ssa_renaming_dtree f dt pid newpids (vm_init ty) in
  if used_in_fdef pid f1 then f1 else remove_fdef pid f1

(** val insert_phis :
    LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.id -> LLVMsyntax.typ
    -> LLVMsyntax.fdef*LLVMsyntax.id list **)

let insert_phis f rd pid ty =
  let preds = make_predecessors (successors f) in
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  let ex_ids = getFdefLocs f in
  let p,newpids =
    fold_left (fun acc b ->
      let y,newpids = acc in
      let bs',ex_ids' = y in
      let LLVMsyntax.Coq_block_intro (l0, ps, cs, tmn) = b in
      (match ATree.get l0 preds with
         | Some pds ->
             (match pds with
                | [] -> ((b::(Obj.magic bs')),ex_ids'),newpids
                | a::l1 ->
                    let pid' = AtomImpl.atom_fresh_for_list ex_ids' in
                    (((LLVMsyntax.Coq_block_intro (l0,
                    ((LLVMsyntax.Coq_insn_phi (pid', ty,
                    (fold_left (fun acc0 p -> LLVMsyntax.Cons_list_value_l
                      ((if in_dec LLVMinfra.l_dec p rd
                        then LLVMsyntax.Coq_value_id pid
                        else LLVMsyntax.Coq_value_const
                               (LLVMsyntax.Coq_const_undef ty)), p, acc0))
                      pds LLVMsyntax.Nil_list_value_l)))::ps), cs,
                    tmn))::bs'),(pid'::ex_ids')),(pid'::
                    (Obj.magic newpids)))
         | None -> ((b::bs'),ex_ids'),newpids)) (rev bs) (([],ex_ids),[])
  in
  let bs',l0 = p in (LLVMsyntax.Coq_fdef_intro (fh, bs')),newpids

(** val is_promotable : LLVMsyntax.fdef -> LLVMsyntax.id -> bool **)

let is_promotable f pid =
  let LLVMsyntax.Coq_fdef_intro (f0, bs) = f in
  fold_left (fun acc b ->
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, tmn) = b in
    if fold_left (fun re p -> if re then true else used_in_phi pid p) ps
         (used_in_tmn pid tmn)
    then false
    else fold_left (fun acc0 c ->
           if used_in_cmd pid c
           then (match c with
                   | LLVMsyntax.Coq_insn_load (i, t0, v, a) -> acc0
                   | LLVMsyntax.Coq_insn_store (i, t0, v, v0, a) ->
                       if negb
                            (LLVMinfra.valueEqB v (LLVMsyntax.Coq_value_id
                              pid))
                       then acc0
                       else false
                   | _ -> false)
           else acc0) cs acc) bs true

(** val find_promotable_alloca :
    LLVMsyntax.fdef -> LLVMsyntax.cmds -> LLVMsyntax.id list ->
    ((LLVMsyntax.id*LLVMsyntax.typ)*LLVMsyntax.align) option **)

let rec find_promotable_alloca f cs dones =
  match cs with
    | [] -> None
    | c::cs' ->
        (match c with
           | LLVMsyntax.Coq_insn_alloca (pid, ty, v, al) ->
               if if is_promotable f pid
                  then negb
                         (proj_sumbool (in_dec LLVMinfra.id_dec pid dones))
                  else false
               then Some ((pid,ty),al)
               else find_promotable_alloca f cs' dones
           | _ -> find_promotable_alloca f cs' dones)

(** val mem2reg_fdef_iter :
    LLVMsyntax.fdef -> coq_DTree -> LLVMsyntax.l list -> LLVMsyntax.id list
    -> (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let mem2reg_fdef_iter f dt rd dones =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
        (match find_promotable_alloca f cs dones with
           | Some p0 ->
               let p1,al = p0 in
               let pid,ty = p1 in
               let f',newpids = insert_phis f rd pid ty in
               ((ssa_renaming f' dt pid ty newpids),true),(pid::dones)
           | None -> (f,false),dones)
    | None -> (f,false),dones

(** val gen_fresh_ids :
    LLVMsyntax.id list -> AtomImpl.atom list ->
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t*AtomImpl.atom list **)

let gen_fresh_ids rd ex_ids =
  fold_left (fun acc l0 ->
    let nids',ex_ids' = acc in
    let lid' = AtomImpl.atom_fresh_for_list ex_ids' in
    let pid' = AtomImpl.atom_fresh_for_list (lid'::ex_ids') in
    let sid' = AtomImpl.atom_fresh_for_list (pid'::(lid'::ex_ids')) in
    (ATree.set l0 ((lid',pid'),sid') nids'),(sid'::(pid'::(lid'::ex_ids'))))
    rd (ATree.empty,ex_ids)

(** val gen_phinode :
    LLVMsyntax.id -> LLVMsyntax.typ ->
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l
    list -> LLVMsyntax.phinode **)

let gen_phinode pid' ty nids pds =
  LLVMsyntax.Coq_insn_phi (pid', ty,
    (fold_left (fun acc p -> LLVMsyntax.Cons_list_value_l
      ((match ATree.get p nids with
          | Some p0 ->
              let p1,i = p0 in
              let lid0,i0 = p1 in LLVMsyntax.Coq_value_id lid0
          | None -> LLVMsyntax.Coq_value_const (LLVMsyntax.Coq_const_undef
              ty)), p, acc)) pds LLVMsyntax.Nil_list_value_l))

(** val phinodes_placement_block :
    LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.align ->
    ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l
    list ATree.t -> LLVMsyntax.l list ATree.t -> LLVMsyntax.block ->
    LLVMsyntax.block **)

let phinodes_placement_block pid ty al nids succs preds b = match b with
  | LLVMsyntax.Coq_block_intro (l0, ps, cs, tmn) ->
      (match ATree.get l0 nids with
         | Some p ->
             let p0,sid = p in
             let lid,pid' = p0 in
             let cs' =
               match ATree.get l0 succs with
                 | Some l1 ->
                     (match l1 with
                        | [] -> []
                        | l2::l3 ->
                            EnvImpl.one (LLVMsyntax.Coq_insn_load (lid, ty,
                              (LLVMsyntax.Coq_value_id pid), al)))
                 | None -> []
             in
             (match ATree.get l0 preds with
                | Some pds ->
                    (match pds with
                       | [] -> LLVMsyntax.Coq_block_intro (l0, ps,
                           (app cs cs'), tmn)
                       | l1::l2 -> LLVMsyntax.Coq_block_intro (l0,
                           ((gen_phinode pid' ty nids pds)::ps),
                           ((LLVMsyntax.Coq_insn_store (sid, ty,
                           (LLVMsyntax.Coq_value_id pid'),
                           (LLVMsyntax.Coq_value_id pid),
                           al))::(app cs cs')), tmn))
                | None -> LLVMsyntax.Coq_block_intro (l0, ps, 
                    (app cs cs'), tmn))
         | None -> b)

(** val phinodes_placement_blocks :
    LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.align
    -> ((LLVMsyntax.id*LLVMsyntax.id)*LLVMsyntax.id) ATree.t -> LLVMsyntax.l
    list ATree.t -> LLVMsyntax.l list ATree.t -> LLVMsyntax.blocks **)

let phinodes_placement_blocks bs pid ty al nids succs preds =
  map (phinodes_placement_block pid ty al nids succs preds) bs

(** val phinodes_placement :
    LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.id -> LLVMsyntax.typ
    -> LLVMsyntax.align -> LLVMsyntax.l list ATree.t -> LLVMsyntax.l list
    ATree.t -> LLVMsyntax.fdef **)

let phinodes_placement f rd pid ty al succs preds =
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  let nids,l0 = gen_fresh_ids rd (getFdefLocs f) in
  let bs1 = phinodes_placement_blocks bs pid ty al nids succs preds in
  LLVMsyntax.Coq_fdef_intro (fh, bs1)

(** val find_init_stld :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id list ->
    ((LLVMsyntax.id*LLVMsyntax.value)*LLVMsyntax.cmds,
    LLVMsyntax.value*LLVMsyntax.cmds) sum option **)

let rec find_init_stld cs pid dones =
  match cs with
    | [] -> None
    | c::cs' ->
        (match c with
           | LLVMsyntax.Coq_insn_alloca (qid, ty, v, a) ->
               if in_dec LLVMinfra.id_dec qid dones
               then find_init_stld cs' pid dones
               else if LLVMinfra.id_dec pid qid
                    then Some (Coq_inr ((LLVMsyntax.Coq_value_const
                           (LLVMsyntax.Coq_const_undef ty)),cs'))
                    else find_init_stld cs' pid dones
           | LLVMsyntax.Coq_insn_store (sid, t0, v0, v, a) ->
               (match v with
                  | LLVMsyntax.Coq_value_id qid ->
                      if in_dec LLVMinfra.id_dec sid dones
                      then find_init_stld cs' pid dones
                      else if LLVMinfra.id_dec pid qid
                           then Some (Coq_inl ((sid,v0),cs'))
                           else find_init_stld cs' pid dones
                  | LLVMsyntax.Coq_value_const c0 ->
                      find_init_stld cs' pid dones)
           | _ -> find_init_stld cs' pid dones)

(** val find_next_stld :
    LLVMsyntax.cmds -> LLVMsyntax.id -> (LLVMsyntax.id,
    LLVMsyntax.id*LLVMsyntax.value) sum option **)

let rec find_next_stld cs pid =
  match cs with
    | [] -> None
    | c::cs' ->
        (match c with
           | LLVMsyntax.Coq_insn_load (lid, t0, v, a) ->
               (match v with
                  | LLVMsyntax.Coq_value_id qid ->
                      if LLVMinfra.id_dec pid qid
                      then Some (Coq_inl lid)
                      else find_next_stld cs' pid
                  | LLVMsyntax.Coq_value_const c0 -> find_next_stld cs' pid)
           | LLVMsyntax.Coq_insn_store (sid, t0, v0, v, a) ->
               (match v with
                  | LLVMsyntax.Coq_value_id qid ->
                      if LLVMinfra.id_dec pid qid
                      then Some (Coq_inr (sid,v0))
                      else find_next_stld cs' pid
                  | LLVMsyntax.Coq_value_const c0 -> find_next_stld cs' pid)
           | _ -> find_next_stld cs' pid)

(** val elim_stld_cmds :
    LLVMsyntax.fdef -> LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.id list
    -> (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let elim_stld_cmds f cs pid dones =
  match find_init_stld cs pid dones with
    | Some s ->
        (match s with
           | Coq_inl p ->
               let p0,cs' = p in
               let sid1,v1 = p0 in
               (match find_next_stld cs' pid with
                  | Some s0 ->
                      (match s0 with
                         | Coq_inl lid ->
                             ((remove_fdef lid (subst_fdef lid v1 f)),true),dones
                         | Coq_inr p1 -> ((remove_fdef sid1 f),true),dones)
                  | None -> (f,true),(sid1::dones))
           | Coq_inr p ->
               let v1,cs' = p in
               (match find_next_stld cs' pid with
                  | Some s0 ->
                      (match s0 with
                         | Coq_inl lid ->
                             ((remove_fdef lid (subst_fdef lid v1 f)),true),dones
                         | Coq_inr p0 -> (f,true),(pid::dones))
                  | None -> (f,true),(pid::dones)))
    | None -> (f,false),dones

(** val elim_stld_blocks :
    LLVMsyntax.fdef -> LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.id
    list -> (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let rec elim_stld_blocks f bs pid dones =
  match bs with
    | [] -> (f,false),dones
    | b::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
        let p0,dones' = elim_stld_cmds f cs pid dones in
        let f',changed = p0 in
        if changed
        then (f',true),dones'
        else elim_stld_blocks f' bs' pid dones

(** val elim_stld_fdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.id list ->
    (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let elim_stld_fdef f pid dones =
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  elim_stld_blocks f bs pid dones

(** val elim_stld_step :
    LLVMsyntax.id -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
    (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
    sum **)

let elim_stld_step pid = function
  | f,dones ->
      let p,dones1 = elim_stld_fdef f pid dones in
      let f1,changed1 = p in
      if changed1 then Coq_inr (f1,dones1) else Coq_inl (f1,dones1)

(** val does_stld_elim : unit -> bool **)

let does_stld_elim = Transforms_aux.does_stld_elim

(** val load_in_cmd : LLVMsyntax.id -> LLVMsyntax.cmd -> bool **)

let load_in_cmd id' = function
  | LLVMsyntax.Coq_insn_load (i, t0, v, a) -> used_in_value id' v
  | _ -> false

(** val load_in_block : LLVMsyntax.id -> LLVMsyntax.block -> bool **)

let load_in_block id' = function
  | LLVMsyntax.Coq_block_intro (l0, p, cs0, t0) ->
      fold_left (fun re c -> if re then true else load_in_cmd id' c) cs0
        false

(** val load_in_fdef : LLVMsyntax.id -> LLVMsyntax.fdef -> bool **)

let load_in_fdef id' = function
  | LLVMsyntax.Coq_fdef_intro (f0, bs) ->
      fold_left (fun re b -> if re then true else load_in_block id' b) bs
        false

(** val elim_dead_st_cmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmds **)

let rec elim_dead_st_cmds cs pid =
  match cs with
    | [] -> []
    | c::cs' ->
        (match c with
           | LLVMsyntax.Coq_insn_store (sid, t0, v, v0, a) ->
               (match v0 with
                  | LLVMsyntax.Coq_value_id qid ->
                      if LLVMinfra.id_dec pid qid
                      then elim_dead_st_cmds cs' pid
                      else c::(elim_dead_st_cmds cs' pid)
                  | LLVMsyntax.Coq_value_const c0 ->
                      c::(elim_dead_st_cmds cs' pid))
           | _ -> c::(elim_dead_st_cmds cs' pid))

(** val elim_dead_st_block :
    LLVMsyntax.id -> LLVMsyntax.block -> LLVMsyntax.block **)

let elim_dead_st_block pid = function
  | LLVMsyntax.Coq_block_intro (l0, ps, cs, tmn) ->
      LLVMsyntax.Coq_block_intro (l0, ps, (elim_dead_st_cmds cs pid), tmn)

(** val elim_dead_st_fdef :
    LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.fdef **)

let elim_dead_st_fdef f pid =
  let LLVMsyntax.Coq_fdef_intro (fh, bs) = f in
  LLVMsyntax.Coq_fdef_intro (fh, (map (elim_dead_st_block pid) bs))

(** val macro_mem2reg_fdef_iter :
    LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.l list ATree.t ->
    LLVMsyntax.l list ATree.t -> LLVMsyntax.id list ->
    (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let macro_mem2reg_fdef_iter f rd succs preds dones =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
        (match find_promotable_alloca f cs dones with
           | Some p0 ->
               let p1,al = p0 in
               let pid,ty = p1 in
               let f1 = phinodes_placement f rd pid ty al succs preds in
               let f2,l1 =
                 if does_stld_elim ()
                 then SafePrimIter.iterate (elim_stld_step pid) (f1,[])
                 else f1,[]
               in
               let f3 =
                 if load_in_fdef pid f2 then f2 else elim_dead_st_fdef f2 pid
               in
               ((if used_in_fdef pid f3 then f3 else remove_fdef pid f3),true),(pid::dones)
           | None -> (f,false),dones)
    | None -> (f,false),dones

(** val macro_mem2reg_fdef_step :
    LLVMsyntax.l list -> LLVMsyntax.l list ATree.t -> LLVMsyntax.l list
    ATree.t -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
    (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
    sum **)

let macro_mem2reg_fdef_step rd succs preds = function
  | f,dones ->
      let p,dones1 = macro_mem2reg_fdef_iter f rd succs preds dones in
      let f1,changed1 = p in
      if changed1 then Coq_inr (f1,dones1) else Coq_inl (f1,dones1)

(** val mem2reg_fdef_step :
    coq_DTree -> LLVMsyntax.l list -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
    (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
    sum **)

let mem2reg_fdef_step dt rd = function
  | f,dones ->
      let p,dones1 = mem2reg_fdef_iter f dt rd dones in
      let f1,changed1 = p in
      if changed1 then Coq_inr (f1,dones1) else Coq_inl (f1,dones1)

(** val remove_redundancy :
    LLVMsyntax.ids -> LLVMsyntax.ids -> LLVMsyntax.ids **)

let rec remove_redundancy acc = function
  | [] -> acc
  | id1::ids0' ->
      if in_dec LLVMinfra.id_dec id1 acc
      then remove_redundancy acc ids0'
      else remove_redundancy (id1::acc) ids0'

(** val eliminate_phi :
    LLVMsyntax.fdef -> LLVMsyntax.phinode -> LLVMsyntax.fdef*bool **)

let eliminate_phi f pn = match pn with
  | LLVMsyntax.Coq_insn_phi (pid, t0, vls) ->
      let vls' = LLVMsyntax.unmake_list_value_l vls in
      let ops = LLVMinfra.values2ids (LLVMinfra.list_prj1 vls') in
      if beq_nat (length ops) (length vls')
      then let ids0 = pid::ops in
           let ndp0 = remove_redundancy [] ids0 in
           (match ndp0 with
              | [] -> f,false
              | id1::l0 ->
                  (match l0 with
                     | [] -> (remove_fdef id1 f),false
                     | id2::l1 ->
                         (match l1 with
                            | [] ->
                                let pid0 = LLVMinfra.getPhiNodeID pn in
                                if LLVMinfra.id_dec pid0 id1
                                then (remove_fdef pid0
                                       (isubst_fdef pid0 id2 f)),true
                                else if LLVMinfra.id_dec pid0 id2
                                     then (remove_fdef pid0
                                            (isubst_fdef pid0 id1 f)),true
                                     else f,false
                            | i::l2 -> f,false)))
      else f,false

(** val eliminate_phis :
    LLVMsyntax.fdef -> LLVMsyntax.phinodes -> LLVMsyntax.fdef*bool **)

let rec eliminate_phis f = function
  | [] -> f,false
  | p::ps' ->
      let f',changed = eliminate_phi f p in
      if changed then f',true else eliminate_phis f' ps'

(** val eliminate_blocks :
    LLVMsyntax.fdef -> LLVMsyntax.blocks -> LLVMsyntax.fdef*bool **)

let rec eliminate_blocks f = function
  | [] -> f,false
  | b::bs' ->
      let LLVMsyntax.Coq_block_intro (l0, ps, c, t0) = b in
      let f',changed = eliminate_phis f ps in
      if changed then f',true else eliminate_blocks f' bs'

(** val eliminate_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef*bool **)

let eliminate_fdef f = match f with
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> eliminate_blocks f bs

(** val eliminate_step :
    LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum **)

let eliminate_step f =
  let f1,changed1 = eliminate_fdef f in
  if changed1 then Coq_inr f1 else Coq_inl f1

(** val does_phi_elim : unit -> bool **)

let does_phi_elim = Transforms_aux.does_phi_elim

(** val does_macro_m2r : unit -> bool **)

let does_macro_m2r = Transforms_aux.does_macro_m2r

(** val mem2reg_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let mem2reg_fdef f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (root, p, cs, t0) = b in
        (match reachablity_analysis f with
           | Some rd ->
               if print_reachablity rd
               then let f1,l0 =
                      if does_macro_m2r ()
                      then let succs = successors f in
                           let preds = make_predecessors succs in
                           SafePrimIter.iterate
                             (macro_mem2reg_fdef_step rd succs preds) (f,[])
                      else let b0 = bound_fdef f in
                           let dts = dom_analyze f in
                           let chains = compute_sdom_chains b0 dts rd in
                           let dt =
                             fold_left (fun acc elt ->
                               let y,chain = elt in
                               create_dtree_from_chain acc chain) chains
                               (DT_node (root, DT_nil))
                           in
                           if if print_dominators b0 dts
                              then print_dtree dt
                              else false
                           then SafePrimIter.iterate
                                  (mem2reg_fdef_step dt rd) (f,[])
                           else f,[]
                    in
                    let f2 =
                      if does_phi_elim ()
                      then SafePrimIter.iterate eliminate_step f1
                      else f1
                    in
                    (match fix_temporary_fdef f2 with
                       | Some f' -> f'
                       | None -> f)
               else f
           | None -> f)
    | None -> f

(** val run : LLVMsyntax.coq_module -> LLVMsyntax.coq_module **)

let run = function
  | LLVMsyntax.Coq_module_intro (los, nts, ps) -> LLVMsyntax.Coq_module_intro
      (los, nts,
      (map (fun p ->
        match p with
          | LLVMsyntax.Coq_product_fdef f -> LLVMsyntax.Coq_product_fdef
              (mem2reg_fdef f)
          | _ -> p) ps))

