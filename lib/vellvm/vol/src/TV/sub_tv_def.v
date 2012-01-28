Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import targetdata.
Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Metatheory.
Require Import sub_symexe.
Require Import trace.
Require Import alist.
Require Import monad.
Require Import opsem.

Export SBSE.
Import LLVMtd.

(* Syntactical equivalence *)
Definition eq_value (v v':value) := sumbool2bool _ _ (value_dec v v').
Definition tv_typ (t t':typ) := sumbool2bool _ _ (typ_dec t t').
Definition tv_align (a a':align) := sumbool2bool _ _ (Align.dec a a').
Definition eq_sterm (st st':sterm) := sumbool2bool _ _ (sterm_dec st st').
Definition eq_smem (sm sm':smem) := sumbool2bool _ _ (smem_dec sm sm').
Definition eq_id (i i':id) := sumbool2bool _ _ (id_dec i i').
Definition eq_const (c c':const) := sumbool2bool _ _ (const_dec c c').
Definition eq_l (l1 l2:l) := sumbool2bool _ _ (l_dec l1 l2).
Definition bzeq (x y:Z) := sumbool2bool _ _ (Coqlib.zeq x y).

Axiom eq_INT_Z : Int -> Z -> bool.

Module SBsyntax.

(* 
   If a function returns a pointer, e.g.
     define i32* @test(i32 %mm) nounwind
   Softbound translates it to be
     define void @softbound_test({ i32*, i8*, i8* }* %shadow_ret, i32 %mm)

   %shadow_ret is a returned pointer with its base and bound.

   At callsite,
     %3 = tail call i32* @test(i32 %2) nounwind
   is translated to be

     call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4   

   The idea is defining an abstract call (insn_call_ptr)
     {%3, %call_repl_base, %call_repl_bound} = 
       call void @softbound_test({ i32*, i8*, i8* }* %ret_tmp, i32 %2)
   that equals to the above seven instructions.

   insn_call_nptr presents a normal call.
*)

Inductive call : Set :=
 | insn_call_nptr : id -> noret -> clattrs -> typ -> value -> params -> call
 | insn_call_ptr : id -> noret -> clattrs -> typ -> value -> params -> 
                id -> id -> id -> id -> id -> id -> id -> 
                const -> const -> const -> call.

Definition sz32 := Size.ThirtyTwo.
Definition i32 := typ_int sz32.
Definition i8 := typ_int Size.Eight.
Definition p32 := typ_pointer i32.
Definition p8 := typ_pointer i8.
Definition pp32 := typ_pointer p32.
Definition pp8 := typ_pointer p8.
Definition cpars c1 c2 := 
  Cons_list_sz_value sz32 (value_const c1) 
  (Cons_list_sz_value sz32 (value_const c2) Nil_list_sz_value).

Definition call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 c0 c1 c2:=
let vret := value_id sid in
let tret := typ_pointer (typ_struct 
  (Cons_list_typ (typ_pointer t) 
  (Cons_list_typ (typ_pointer p8)
  (Cons_list_typ (typ_pointer p8) Nil_list_typ)))) in
(insn_call_nptr rid nr tc t v ((tret,nil,vret)::p),
 insn_gep id1 false tret vret (cpars c0 c0)::
 insn_load id2 pp32 (value_id id1) Align.One::
 insn_gep id3 false tret vret (cpars c0 c1)::
 insn_load id4 pp32 (value_id id3) Align.One::
 insn_gep id5 false tret vret (cpars c0 c2)::
 insn_load id6 pp32 (value_id id5) Align.One::nil).

Record subblock := mkSB
{
  NBs : list nbranch;
  call_cmd : call
}.

(*
  For a function that returns a pointer, Softbound translates
         ret i32* %8                                                           
  into
         %.ptr = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 0
         %.base = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 1
         store i8* %bitcast, i8** %.base
         %.bound = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 2
         store i8* %bitcast4, i8** %.bound
         store i32* %8, i32** %.ptr
         ret void
 
  insn_return_ptr %shadow_ret %.base %.base %.ptr i32
*)
Inductive iterminator : Set := 
 | insn_return_ptr : id -> typ -> id -> id -> id -> value -> id -> id -> value ->
     id -> value -> id -> const -> const -> const -> iterminator.

Definition ret_ptr sid t id1 id2 id30 v3 id4 id50 v5 id60 v6 id7 c0 c1 c2 :=
let vret := value_id sid in
let tret := typ_pointer (typ_struct 
  (Cons_list_typ (typ_pointer t)
  (Cons_list_typ (typ_pointer p8)
  (Cons_list_typ (typ_pointer p8) Nil_list_typ)))) in
(insn_gep id1 false tret vret (cpars c0 c0)::
 insn_gep id2 false tret vret (cpars c0 c1)::
 insn_store id30 p8 v3 (value_id id2) Align.One::
 insn_gep id4 false tret vret (cpars c0 c2)::
 insn_store id50 p8 v5 (value_id id4) Align.One::
 insn_store id60 (typ_pointer t) v6 (value_id id1) Align.One::nil,
 insn_return_void id7).

Inductive block : Set := 
 | block_common : l -> phinodes -> list subblock -> list nbranch -> 
     terminator -> block
 | block_ret_ptr : l -> phinodes -> list subblock -> list nbranch -> 
     iterminator -> block.

Definition blocks : Set := (list block).

Inductive fdef : Set := 
 | fdef_intro : fheader -> blocks -> fdef.

Inductive product : Set := 
 | product_gvar : gvar -> product
 | product_fdec : fdec -> product
 | product_fdef : fdef -> product.

Definition products : Set := (list product).

Inductive module : Set := 
 | module_intro : layouts -> namedts -> products -> module.

Definition modules : Set := (list module).

Definition system : Set := modules.

Definition isCall_inv : forall (c:cmd), isCall c = true -> 
  id * noret * clattrs * typ * value * params.
destruct c; intros H; try solve [inversion H].
  split; auto.
Defined. 

(*
     %3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 0
     %4 = load i32** %3          
     %_base3 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 1
     %call_repl_base = load i8** %_base3       
     %_bound4 = getelementptr { i32*, i8*, i8* }* %ret_tmp, i32 0, i32 2
     %call_repl_bound = load i8** %_bound4    
*)

(* Check if tid is { i32*, i8*, i8* } *)
Fixpoint get_named_ret_typs nts tid {struct nts} : option (typ*typ*typ) :=
match nts with
| nil => None
| namedt_intro tid' t'::nts' =>
    if (eq_id tid tid') then
      match t' with
      | typ_namedt t0 => get_named_ret_typs nts' tid
      | typ_struct 
         (Cons_list_typ (typ_pointer _ as t01) 
         (Cons_list_typ (typ_pointer _ as t02)
         (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) =>
         Some (t01,t02,t03)
      | _ => None
      end
    else get_named_ret_typs nts' tid
end.

(* Check if t is { i32*, i8*, i8* } *)
Fixpoint get_ret_typs nts t: option (typ*typ*typ) :=
match t with
| typ_struct 
    (Cons_list_typ (typ_pointer _ as t01) 
    (Cons_list_typ (typ_pointer _ as t02)
    (Cons_list_typ (typ_pointer _ as t03) Nil_list_typ))) =>
      Some (t01,t02,t03)
| typ_namedt tid => get_named_ret_typs nts tid
| _ => None
end.

(* Constructing a icall_ptr from the six instructions. *)
Definition gen_icall nts pa1 (c1 c2 c3 c4 c5 c6:cmd) : 
  option (params*id*id*id*id*id*id*id*const*const*const*typ) :=
match c1 with
|LLVMsyntax.insn_gep id11 _ t1 (value_id id12)
   (Cons_list_sz_value _ (value_const (const_int _ i11 as c11)) 
     (Cons_list_sz_value _ (value_const (const_int _ i12 as c12)) 
      Nil_list_sz_value)) =>
  match c2 with
  |LLVMsyntax.insn_load id21 t2 (value_id id22) _ =>
    match c3 with 
    |LLVMsyntax.insn_gep id31 _ t3 (value_id id32) 
       (Cons_list_sz_value _ (value_const (const_int _ i31 as c31)) 
         (Cons_list_sz_value _ (value_const (const_int _ i32 as c32)) 
         Nil_list_sz_value)) =>
      match c4 with
      |LLVMsyntax.insn_load id41 t4 (value_id id42) _ =>
        match c5 with
        |LLVMsyntax.insn_gep id51 _ t5 (value_id id52)
           (Cons_list_sz_value _ (value_const (const_int _ i51 as c51)) 
           (Cons_list_sz_value _ (value_const (const_int _ i52 as c52)) 
              Nil_list_sz_value)) =>
           match c6 with
           |LLVMsyntax.insn_load id61 t6 (value_id id62) _ =>
              match pa1 with
              | (typ_pointer t0, _, value_id id0)::pa1' =>
                if (tv_typ t1 t3 && tv_typ t3 t5 && tv_typ t5 t0 &&
                    eq_id id0 id12 && eq_id id0 id32 && eq_id id0 id52 &&
                    eq_id id11 id22 && eq_id id31 id42 && eq_id id51 id62 &&
                    eq_const c11 c12 && eq_const c11 c31 && eq_const c11 c51 &&
                    eq_INT_Z i11 0%Z && eq_INT_Z i32 1%Z && eq_INT_Z i52 2%Z
                   ) 
                then 
                  match get_ret_typs nts t0 with
                  | Some (t01, t02, t03) => 
                    if (tv_typ t2 t01 && tv_typ t4 t02 && 
                        tv_typ t6 t03 && tv_typ t02 t03 &&
                        tv_typ t02 (typ_pointer (typ_int Size.Eight))) then
                      Some (pa1',id12,id11,id21,id31,id41,id51,id61,
                            c12,c32,c52,t01)
                    else None
                  | _ => None
                  end
                else None
              | _ => None
              end
           | _ => None
           end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end
| _ => None
end.

Fixpoint of_llvm_cmds (nts:namedts) (cs:cmds) : (list subblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCall_dec c) with
  | left isnotcall => 
    match (of_llvm_cmds nts cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkSB nbs call0::sbs', nbs0) => 
      (mkSB (mkNB c isnotcall::nbs) call0::sbs', nbs0) 
    end
  | right iscall => 
    let '(id1, nr1, tc1, t1, v1, pa1) := isCall_inv c iscall in
    let '(sbs, nbs0, ic) :=
(*
    The [c] is in the output program. So we don't know if it returns pointer
    w/o its signature in its input.

    But we do not check if the called function returns ptr. The problem is
    v1 can be a value that represents a function pointer. Statically, we 
    need more work to identify it.

    We check this property at tv_call.
*)
      if (tv_typ t1 typ_void) then
        match cs' with
        | c1::c2::c3::c4::c5::c6::cs'' =>
          match (gen_icall nts pa1 c1 c2 c3 c4 c5 c6) with
          | Some (pa1',id12,id11,id21,id31,id41,id51,id61,cst0,cst1,cst2,rt) => 
             (of_llvm_cmds nts cs'', 
              insn_call_ptr id1 nr1 tc1 rt v1 pa1' 
              id12 id11 id21 id31 id41 id51 id61 cst0 cst1 cst2)
          | None => (of_llvm_cmds nts cs', insn_call_nptr id1 nr1 tc1 t1 v1 pa1)
          end
        | _ => (of_llvm_cmds nts cs', insn_call_nptr id1 nr1 tc1 t1 v1 pa1)
        end
      else (of_llvm_cmds nts cs', insn_call_nptr id1 nr1 tc1 t1 v1 pa1)
    in (mkSB nil ic::sbs, nbs0) 
  end
end.

(*
  For a function that returns a pointer, Softbound translates
         ret i32* %8                                                           
  into
         %.ptr = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 0
         %.base = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 1
         store i8* %bitcast, i8** %.base
         %.bound = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 2
         store i8* %bitcast4, i8** %.bound
         store i32* %8, i32** %.ptr
          ret void
 
  gen_iret returns %shadow_ret %.base %.base %.ptr i32* 
*)
Definition gen_iret nts t0 id0 (c1 c2 c3 c4 c5 c6:cmd) (id7:id) :=
match c1 with
|LLVMsyntax.insn_gep id11 _ t1 (value_id id12)
   (Cons_list_sz_value _ (value_const (const_int _ i11 as c11)) 
     (Cons_list_sz_value _ (value_const (const_int _ i12 as c12)) 
      Nil_list_sz_value)) =>
  match c2 with 
  |LLVMsyntax.insn_gep id21 _ t2 (value_id id22) 
     (Cons_list_sz_value _ (value_const (const_int _ i21 as c21)) 
       (Cons_list_sz_value _ (value_const (const_int _ i22 as c22)) 
       Nil_list_sz_value)) =>
    match c3 with
    |LLVMsyntax.insn_store id31 t3 v3 (value_id id32) _ =>
      match c4 with
      |LLVMsyntax.insn_gep id41 _ t4 (value_id id42)
         (Cons_list_sz_value _ (value_const (const_int _ i41 as c41)) 
         (Cons_list_sz_value _ (value_const (const_int _ i42 as c42)) 
            Nil_list_sz_value)) =>
        match c5 with
        |LLVMsyntax.insn_store id51 t5 v5 (value_id id52) _ =>
           match c6 with
           |LLVMsyntax.insn_store id61 t6 v6 (value_id id62) _ =>
              if (tv_typ t0 (typ_pointer t1) && tv_typ t1 t2 && tv_typ t2 t4 &&
                  eq_id id0 id12 && eq_id id12 id22 && eq_id id22 id42 &&
                  eq_id id11 id62 && eq_id id21 id32 && eq_id id41 id52 &&
                  eq_const c11 c12 && eq_const c11 c21 && eq_const c11 c41 &&
                  eq_INT_Z i11 0%Z && eq_INT_Z i22 1%Z && eq_INT_Z i42 2%Z
                 ) 
              then 
                match get_ret_typs nts t1 with
                | Some (t01, t02, t03) => 
                    if (tv_typ t6 t01 && tv_typ t3 t02 && 
                        tv_typ t5 t03 && tv_typ t02 t03 &&
                        tv_typ t02 (typ_pointer (typ_int Size.Eight))) then
                      Some (id12,t6,id11,id21,id31,v3,id41,id51,v5,id61,v6,id7,
                            c12,c22,c42)
                    else None
                | None => None
                end
              else None
           | _ => None
           end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end
| _ => None
end.

Definition get_last_six_insns (cs:cmds) :=
match (List.rev cs) with
| c6::c5::c4::c3::c2::c1::cs' => (List.rev cs', Some (c1, c2, c3, c4, c5, c6))
| _ => (cs, None)
end.

(* FIXME: Although layouts * namedts = TargetData, TargetData is extracted
   to be LLVM.TargetData. So we must use layouts * namedts to prevent Coq 
   replacing it.
*)
Definition of_llvm_block (TD:layouts * namedts) fd (b:LLVMsyntax.block) : block 
  :=
let '(los, nts) := TD in
let '(LLVMsyntax.block_intro l1 ps1 cs1 tmn1) := b in
let '(cs1', op) :=
  match fd with
  | fheader_intro _ _ _ ((t2,_,id2)::_) _ =>
     match tmn1 with
     | LLVMsyntax.insn_return_void id7 =>
       let '(cs1', opcs6) := get_last_six_insns cs1 in
       match opcs6 with
       | Some (c1,c2,c3,c4,c5,c6) => 
         (* gaen_iret returns %shadow_ret %.base %.base %.ptr i32 *)
         match gen_iret nts t2 id2 c1 c2 c3 c4 c5 c6 id7 with
         | None => (cs1, None)
         | op => (cs1', op)
         end
       | None => (cs1, None)
       end
     | _ => (cs1, None)
     end
  | _ => (cs1, None)
  end in
let '(sbs2, cs2) := of_llvm_cmds nts cs1' in
match op with
| Some (sid,t,id1,id2,id30,v3,id4,id50,v5,id60,v6,id7,cst0,cst1,cst2) =>
    block_ret_ptr l1 ps1 sbs2 cs2
      (insn_return_ptr sid t id1 id2 id30 v3 id4 id50 v5 id60 v6 id7
        cst0 cst1 cst2)
| None => block_common l1 ps1 sbs2 cs2 tmn1
end.

Definition of_llvm_fdef TD (f:LLVMsyntax.fdef) : fdef :=
let '(LLVMsyntax.fdef_intro (fheader_intro fa t fid la va) lb) := f in
fdef_intro (fheader_intro fa t fid la va) 
  (List.map (of_llvm_block TD (fheader_intro fa t fid la va)) lb).

Fixpoint of_llvm_products TD (Ps:LLVMsyntax.products) : products :=
match Ps with
| nil => nil
| LLVMsyntax.product_gvar g::Ps' => product_gvar g::of_llvm_products TD Ps'
| LLVMsyntax.product_fdec f::Ps' => product_fdec f::of_llvm_products TD Ps'
| LLVMsyntax.product_fdef f::Ps' => 
    product_fdef (of_llvm_fdef TD f):: of_llvm_products TD Ps'
end.

Definition of_llvm_module (m:LLVMsyntax.module) : module :=
let '(LLVMsyntax.module_intro los nts Ps) := m in
module_intro los nts (of_llvm_products (los,nts) Ps).

Definition of_llvm_system (s:LLVMsyntax.system) : system :=
List.map of_llvm_module s.

Definition call_to_llvm_cmds (c:call) : cmds :=
match c with
| insn_call_nptr rid nr ca t v p => [insn_call rid nr ca t v p]
| insn_call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 c0 c1 c2 =>
  let vret := value_id sid in
  let tret := typ_pointer (typ_struct 
    (Cons_list_typ (typ_pointer t) 
    (Cons_list_typ (typ_pointer p8)
    (Cons_list_typ (typ_pointer p8) Nil_list_typ)))) in
  (insn_call rid nr tc t v ((tret,nil,vret)::p)::
   insn_gep id1 false tret vret (cpars c0 c0)::
   insn_load id2 pp32 (value_id id1) Align.One::
   insn_gep id3 false tret vret (cpars c0 c1)::
   insn_load id4 pp32 (value_id id3) Align.One::
   insn_gep id5 false tret vret (cpars c0 c2)::
   insn_load id6 pp32 (value_id id5) Align.One::nil)
end.

Definition subblock_to_llvm_cmds (sb:subblock) : cmds :=
let '(mkSB cs c) := sb in
List.map nbranching_cmd cs ++ call_to_llvm_cmds c.

Definition ret_ptr_to_tmn sid t id1 id2 id30 v3 id4 id50 v5 id60 v6 id7 c0 c1 c2
  :=
  let vret := value_id sid in
  let tret := typ_pointer (typ_struct 
    (Cons_list_typ (typ_pointer t)
    (Cons_list_typ (typ_pointer p8)
    (Cons_list_typ (typ_pointer p8) Nil_list_typ)))) in
  (insn_gep id1 false tret vret (cpars c0 c0)::
   insn_gep id2 false tret vret (cpars c0 c1)::
   insn_store id30 p8 v3 (value_id id2) Align.One::
   insn_gep id4 false tret vret (cpars c0 c2)::
   insn_store id50 p8 v5 (value_id id4) Align.One::
   insn_store id60 (typ_pointer t) v6 (value_id id1) Align.One::nil,
   insn_return_void id7).

Definition itmn_to_llvm_tmn : iterminator -> cmds * LLVMsyntax.terminator.
  destruct 1.
  apply (@ret_ptr_to_tmn i0 t i1 i2 i3 v i4 i5 v0 i6 v1 i7 c c0 c1).
Defined.

Definition to_llvm_block (b:block) : LLVMsyntax.block :=
match b with
| block_common l1 ps1 sbs cs tmn =>
  LLVMsyntax.block_intro l1 ps1 
   ((List.fold_left 
      (fun accum => fun sb => accum ++ subblock_to_llvm_cmds sb) sbs nil) ++ 
    (List.map nbranching_cmd cs)) tmn
| block_ret_ptr l1 ps1 sbs cs tmn =>
  let '(cs0,tmn0) := itmn_to_llvm_tmn tmn in
  LLVMsyntax.block_intro l1 ps1 
   ((List.fold_left 
      (fun accum => fun sb => accum ++ subblock_to_llvm_cmds sb) sbs nil) ++ 
    (List.map nbranching_cmd cs) ++ cs0) tmn0
end.

Definition to_llvm_fdef (f:fdef) : LLVMsyntax.fdef :=
let '(fdef_intro fh bs) := f in
LLVMsyntax.fdef_intro fh (List.map to_llvm_block bs).

Definition to_llvm_product (P:product) : LLVMsyntax.product :=
match P with
| product_gvar g => LLVMsyntax.product_gvar g 
| product_fdec f => LLVMsyntax.product_fdec f 
| product_fdef f => LLVMsyntax.product_fdef (to_llvm_fdef f)
end.

Definition to_llvm_products (Ps:products) : LLVMsyntax.products :=
List.map to_llvm_product Ps.

Definition to_llvm_module (m:module) : LLVMsyntax.module :=
let '(module_intro los nts Ps) := m in
LLVMsyntax.module_intro los nts (to_llvm_products Ps).

Definition to_llvm_system (s:system) : LLVMsyntax.system :=
List.map to_llvm_module s.

Inductive wf_inbranchs : list nbranch -> Prop :=
| wf_inbranchs_intro : forall TD cs nbs, 
  of_llvm_cmds TD cs = (nil, nbs) ->
  NoDup (getCmdsIDs cs) ->
  wf_inbranchs nbs.

Inductive wf_isubblock : subblock -> Prop :=
| wf_isubblock_intro : forall nbs call0, 
  wf_inbranchs nbs ->
  wf_isubblock (mkSB nbs call0).

Inductive wf_isubblocks : list subblock -> Prop :=
| wf_isubblocks_nil : wf_isubblocks nil
| wf_isubblocks_cons : forall sb sbs,
  wf_isubblock sb ->
  wf_isubblocks sbs ->
  wf_isubblocks (sb::sbs).

Inductive wf_iblock : block -> Prop :=
| wf_iblock_common : forall l ps cs sbs nbs tmn, 
  wf_isubblocks sbs ->
  wf_inbranchs nbs ->
  wf_iblock (block_common l ps sbs cs tmn)
| wf_iblock_ret_ptr : forall l ps cs sbs nbs tmn, 
  wf_isubblocks sbs ->
  wf_inbranchs nbs ->
  wf_iblock (block_ret_ptr l ps sbs cs tmn).

Hint Constructors wf_isubblocks.


Definition getFheader (fd:fdef) : fheader :=
let '(fdef_intro fh _) := fd in fh.

  Definition l2block := list (l*block).

  Definition genLabel2Block_block (b:block) : l2block :=
  match b with
  | block_common l _ _ _ _ => (l,b)::nil
  | block_ret_ptr l _ _ _ _ => (l,b)::nil
  end.  

  Fixpoint genLabel2Block_blocks (bs:blocks) : l2block :=
  match bs with 
  | nil => nil
  | b::bs' => (genLabel2Block_block b)++(genLabel2Block_blocks bs')
  end.

  Definition genLabel2Block_fdef (f:fdef) : l2block := 
  match f with
  | fdef_intro fheader blocks => genLabel2Block_blocks blocks
  end.

  Definition lookupBlockViaLabelFromFdef (f:fdef) (l0:l) : option block :=
  lookupAL _ (genLabel2Block_fdef f) l0.  

Definition getPHINodesFromBlock (b:block) : list phinode :=
match b with
| (block_common _ lp _ _ _) => lp
| (block_ret_ptr _ lp _ _ _) => lp
end.

Definition getValueViaBlockFromValuels (vls:list_value_l) (b:block) : option value :=
match b with
| block_common l _ _ _ _ => getValueViaLabelFromValuels vls l
| block_ret_ptr l _ _ _ _ => getValueViaLabelFromValuels vls l
end.

Definition getValueViaBlockFromPHINode (i:phinode) (b:block) : option value :=
match i with
| insn_phi _ _ vls => getValueViaBlockFromValuels vls b
end.

Fixpoint getIncomingValuesForBlockFromPHINodes (TD:TargetData)
  (PNs:list phinode) (b:block) (globals locals:GVMap) : 
  option (list (id*GenericValue)) :=
match PNs with
| nil => Some nil
| (insn_phi id0 t vls)::PNs => 
  match (getValueViaBlockFromPHINode (insn_phi id0 t vls) b) with
  | None => None
  | Some (value_id id1) => 
      match (lookupAL _ locals id1, 
             getIncomingValuesForBlockFromPHINodes TD PNs b globals locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end               
  | Some (value_const c) => 
      match (const2GV TD globals c, 
             getIncomingValuesForBlockFromPHINodes TD PNs b globals locals)
      with
      | (Some gv1, Some idgvs) => Some ((id0,gv1)::idgvs)
      | _ => None
      end
  end
end.

Fixpoint updateValuesForNewBlock (ResultValues:list (id*GenericValue)) 
  (locals:GVMap) : GVMap :=
match ResultValues with
| nil => locals
| (id, v)::ResultValues' => 
    updateAddAL _ (updateValuesForNewBlock ResultValues' locals) id v
end.

Definition switchToNewBasicBlock (TD:TargetData) (Dest:block) 
  (PrevBB:block) (globals locals:GVMap): option GVMap :=
  let PNs := getPHINodesFromBlock Dest in
  match getIncomingValuesForBlockFromPHINodes TD PNs PrevBB globals locals with
  | Some ResultValues => Some (updateValuesForNewBlock ResultValues locals)
  | None => None
  end.

Definition lookupFdecViaIDFromProduct (p:product) (i:id) : option fdec :=
match p with
| (product_fdec fd) => if eq_dec (getFdecID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdecViaIDFromProducts (lp:products) (i:id) : option fdec :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdecViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromProducts lp' i
  end
end.

Definition getFdefID (fd:fdef) : id :=
match fd with
| fdef_intro fh _ => getFheaderID fh
end.

Definition lookupFdefViaIDFromProduct (p:product) (i:id) : option fdef :=
match p with
| (product_fdef fd) => if eq_dec (getFdefID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdefViaIDFromProducts (lp:products) (i:id) : option fdef :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdefViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromProducts lp' i
  end
end.

Fixpoint lookupFdefViaGVFromFunTable (fs:GVMap) (fptr:GenericValue) : option id 
  :=
match fs with
| nil => None
| (id0,gv0)::fs' => 
  if eq_gv gv0 fptr
  then Some id0 
  else lookupFdefViaGVFromFunTable fs' fptr
end.

Definition lookupExFdecViaGV (TD:TargetData) (Ps:products) (gl lc:GVMap)
  (fs:GVMap) (fv:value) : option fdec :=
do fptr <- getOperandValue TD fv lc gl;
do fn <- lookupFdefViaGVFromFunTable fs fptr;
    match lookupFdefViaIDFromProducts Ps fn with 
    | Some _ => None
    | None => lookupFdecViaIDFromProducts Ps fn
    end
.

Definition lookupFdefViaGV (TD:TargetData) (Ps:products) (gl lc:GVMap) 
  (fs:GVMap) (fv:value) : option fdef :=
match getOperandValue TD fv lc gl with
| Some fptr =>
  match OpsemAux.lookupFdefViaGVFromFunTable fs fptr with
  | Some fn => lookupFdefViaIDFromProducts Ps fn
  | None => None
  end
| None => None
end.

Definition getEntryBlock fd :=
match fd with
| fdef_intro _ nil => None
| fdef_intro _ (b :: _) => Some b
end.

Fixpoint lookupGvarViaIDFromProducts (lp:SBsyntax.products) (i:id) 
  : option gvar :=
match lp with
| nil => None
| (SBsyntax.product_gvar gv)::lp' => 
    if (eq_dec (getGvarID gv) i) then Some gv
    else lookupGvarViaIDFromProducts lp' i
| _::lp' => lookupGvarViaIDFromProducts lp' i
end.

Definition lookupGvarFromProduct (p:SBsyntax.product) (id:id) : option gvar :=
match p with
| SBsyntax.product_gvar (gvar_intro id' lk spec t c a) =>
  match (eq_dec id id') with
  | left _ => Some (gvar_intro id' lk spec t c a)
  | right _ => None
  end
| SBsyntax.product_gvar (gvar_external id' spec t) =>
  match (eq_dec id id') with
  | left _ => Some (gvar_external id' spec t)
  | right _ => None
  end
| _ => None
end.  

Fixpoint lookupGvarFromProducts (lp:SBsyntax.products) (id:id) 
  : option gvar :=
match lp with
| nil => None
| p::lp' => 
  match (lookupGvarFromProduct p id) with
  | None => lookupGvarFromProducts lp' id
  | re => re
  end
end.

Fixpoint lookupFdecFromProducts (lp:SBsyntax.products) (id1:id) : option fdec :=
match lp with
| nil => None
| SBsyntax.product_fdec (fdec_intro (fheader_intro _ _ fid _ _) as f)::lp' => 
    if eq_dec id1 fid then Some f
    else lookupFdecFromProducts lp' id1
| _::lp' => lookupFdecFromProducts lp' id1
end.

End SBsyntax.

Module SBopsem.

Export SBsyntax.

(*************************************************)
(* A new opsem for proofs *)

Definition exCallUpdateLocals TD ft (noret:bool) (rid:id) 
  (oResult:option GenericValue) (lc :GVMap) : option GVMap :=
  match noret with
  | false =>
      match oResult with
      | None => None
      | Some Result => 
          match ft with
          | typ_function t _ _ => 
            match fit_gv TD t Result with
            | Some gr => Some (updateAddAL _ lc rid (? gr # t ?))
            | _ => None
            end
          | _ => None
          end
      end
  | true => Some lc
  end.

Inductive dbCmd : TargetData -> GVMap ->
                  GVMap -> list mblock -> mem -> 
                  cmd -> 
                  GVMap -> list mblock -> mem -> 
                  trace -> SBSE.Result -> Prop :=
| dbBop: forall TD lc gl id bop sz v1 v2 gv3 Mem als,
  BOP TD lc gl bop sz v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_bop id bop sz v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil SBSE.Rok
| dbFBop: forall TD lc gl id fbop fp v1 v2 gv3 Mem als,
  FBOP TD lc gl fbop fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fbop id fbop fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil SBSE.Rok 
| dbExtractValue : forall TD lc gl id t v gv gv' Mem als idxs,
  getOperandValue TD v lc gl = Some gv ->
  extractGenericValue TD t gv idxs = Some gv' ->
  dbCmd TD gl
    lc als Mem
    (insn_extractvalue id t v idxs)
    (updateAddAL _ lc id gv') als Mem
    trace_nil SBSE.Rok 
| dbInsertValue : forall TD lc gl id t v t' v' gv gv' gv'' idxs Mem als,
  getOperandValue TD v lc gl = Some gv ->
  getOperandValue TD v' lc gl = Some gv' ->
  insertGenericValue TD t gv idxs t' gv' = Some gv'' ->
  dbCmd TD gl
    lc als Mem
    (insn_insertvalue id t v t' v' idxs)
    (updateAddAL _ lc id gv'') als Mem
    trace_nil SBSE.Rok 
| dbMalloc : forall TD lc gl id t v gn align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_malloc id t v align)
    (updateAddAL _ lc id (blk2GV TD mb)) als Mem'
    trace_nil SBSE.Rok
| dbFree : forall TD lc gl fid t v Mem als Mem' mptr,
  getOperandValue TD v lc gl = Some mptr ->
  free TD Mem mptr = Some Mem'->
  dbCmd TD gl
    lc als Mem
    (insn_free fid t v)
    lc als Mem'
    trace_nil SBSE.Rok
| dbAlloca : forall TD lc gl id t v gn align Mem als Mem' tsz mb,
  getTypeAllocSize TD t = Some tsz ->
  getOperandValue TD v lc gl = Some gn ->
  malloc TD Mem tsz gn align = Some (Mem', mb) ->
  dbCmd TD gl
    lc als Mem
    (insn_alloca id t v align)
    (updateAddAL _ lc id (blk2GV TD mb)) (mb::als) Mem'
    trace_nil SBSE.Rok
| dbLoad : forall TD lc gl id t v align Mem als mp gv,
  getOperandValue TD v lc gl = Some mp ->
  mload TD Mem mp t align = Some gv ->
  dbCmd TD gl
    lc als Mem
    (insn_load id t v align)
    (updateAddAL _ lc id gv) als Mem
    trace_nil SBSE.Rok
| dbStore : forall TD lc gl sid t v1 v2 align Mem als mp2 gv1 Mem',
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some mp2 ->
  mstore TD Mem mp2 t gv1 align = Some Mem' ->
  dbCmd TD gl 
    lc als Mem
    (insn_store sid t v1 v2 align)
    lc als Mem'
    trace_nil SBSE.Rok
| dbGEP : forall TD lc gl id inbounds t v idxs vidxs mp mp' Mem als,
  getOperandValue TD v lc gl = Some mp ->
  values2GVs TD idxs lc gl = Some vidxs ->
  GEP TD t mp vidxs inbounds = Some mp' ->
  dbCmd TD gl
    lc als Mem
    (insn_gep id inbounds t v idxs)
    (updateAddAL _ lc id mp') als Mem
    trace_nil SBSE.Rok 
| dbTrunc : forall TD lc gl id truncop t1 v1 t2 gv2 Mem als,
  TRUNC TD lc gl truncop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_trunc id truncop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil SBSE.Rok
| dbExt : forall TD lc gl id extop t1 v1 t2 gv2 Mem als,
  EXT TD lc gl extop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_ext id extop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil SBSE.Rok
| dbCast : forall TD lc gl id castop t1 v1 t2 gv2 Mem als,
  CAST TD lc gl castop t1 v1 t2 = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_cast id castop t1 v1 t2)
    (updateAddAL _ lc id gv2) als Mem
    trace_nil SBSE.Rok
| dbIcmp : forall TD lc gl id cond t v1 v2 gv3 Mem als,
  ICMP TD lc gl cond t v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_icmp id cond t v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil SBSE.Rok
| dbFcmp : forall TD lc gl id fcond fp v1 v2 gv3 Mem als,
  FCMP TD lc gl fcond fp v1 v2 = Some gv3 ->
  dbCmd TD gl
    lc als Mem
    (insn_fcmp id fcond fp v1 v2)
    (updateAddAL _ lc id gv3) als Mem
    trace_nil SBSE.Rok
| dbSelect : forall TD lc gl id v0 t v1 v2 cond Mem als gv1 gv2,
  getOperandValue TD v0 lc gl = Some cond ->
  getOperandValue TD v1 lc gl = Some gv1 ->
  getOperandValue TD v2 lc gl = Some gv2 ->
  dbCmd TD gl
    lc als Mem
    (insn_select id v0 t v1 v2)
    (if isGVZero TD cond then updateAddAL _ lc id gv2 
     else updateAddAL _ lc id gv1) als Mem
    trace_nil SBSE.Rok
| dbLib : forall TD lc gl rid noret tailc ft fid 
                          lp rt Mem oresult Mem' als r lc' gvs,
  (* Like isCall, we only consider direct call to libraries. Function pointers
     are conservatively taken as non-lib. The dbCmd is defined to prove the
     correctness of TV. So it should be as "weak" as the TV. *)
  params2GVs TD lp lc gl = Some gvs ->
  SBSE.callLib Mem fid gvs = Some (oresult, Mem', r)
    ->
  exCallUpdateLocals TD ft noret rid oresult lc = Some lc' ->
  dbCmd TD gl
    lc als Mem
    (insn_call rid noret tailc rt (value_const (const_gid ft fid)) lp)
    lc' als Mem'
    trace_nil r
.

Inductive dbCmds : TargetData -> GVMap -> 
                   GVMap -> list mblock -> mem -> 
                   list cmd -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Result -> Prop :=
| dbCmds_nil : forall TD lc als gl Mem, 
    dbCmds TD gl lc als Mem nil lc als Mem trace_nil Rok
| dbCmds_cons : forall TD c cs gl lc1 als1 Mem1 t1 t2 lc2 als2 Mem2
                       lc3 als3 Mem3 r,
    dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 t1 Rok ->
    dbCmds TD gl lc2 als2 Mem2 cs lc3 als3 Mem3 t2 r ->
    dbCmds TD gl lc1 als1 Mem1 (c::cs) lc3 als3 Mem3 (trace_app t1 t2) r
| dbCmds_cons_abort : forall TD c cs gl lc1 als1 Mem1 t1 lc2 als2 Mem2,
    dbCmd TD gl lc1 als1 Mem1 c lc2 als2 Mem2 t1 Rabort ->
    dbCmds TD gl lc1 als1 Mem1 (c::cs) lc2 als2 Mem2 t1 Rabort
.

Inductive dbNbranches : TargetData -> GVMap -> 
                   GVMap -> list mblock -> mem -> 
                   list nbranch -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Result -> Prop :=
| dbNbranches_intro : forall TD cs gl lc1 als1 Mem1 lc2 als2 Mem2 tr r,
    dbCmds TD gl lc1 als1 Mem1 (List.map nbranching_cmd cs) lc2 als2 Mem2 tr r ->
    dbNbranches TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr r.

Inductive dbTerminator : 
  TargetData -> mem -> fdef -> GVMap -> 
  block -> GVMap -> 
  terminator -> 
  block -> GVMap -> 
  trace -> Prop :=
| dbBranch : forall TD Mem F B lc gl bid Cond l1 l2 c B' lc',   
  getOperandValue TD Cond lc gl = Some c ->
  Some B' = (if isGVZero TD c
    then (lookupBlockViaLabelFromFdef F l2)
    else (lookupBlockViaLabelFromFdef F l1)) ->
  Some lc' = switchToNewBasicBlock TD B' B gl lc ->
  dbTerminator TD Mem F gl B lc (insn_br bid Cond l1 l2) B' lc' trace_nil 
| dbBranch_uncond : forall TD Mem F B lc gl l bid B' lc',   
  Some B' = lookupBlockViaLabelFromFdef F l ->
  Some lc' = switchToNewBasicBlock TD B' B gl lc ->
  dbTerminator TD Mem F gl B lc (insn_br_uncond bid l) B' lc' trace_nil 
.

Record ExecutionContext : Type := mkEC
  { CurBB : block;  Locals : GVMap;  Allocas : list mblock }.

Record State : Type := mkState { Frame : ExecutionContext;  Mem : mem }.

Definition callUpdateLocals (TD:TargetData) ft (noret:bool) (rid:id) 
  (oResult:option value) (lc lc' gl:GVMap) : option GVMap :=
    match noret with
    | false =>
        match oResult with
        | None => None
        | Some Result => 
          match getOperandValue TD Result lc' gl with 
          | Some gr =>  
            match ft with
            | typ_function t _ _ => 
              match fit_gv TD t gr with
              | Some gr' => Some (updateAddAL _ lc rid (? gr' # t ?))
              | None => None
              end
            | _ => None
            end
          | None => None
          end
        end
    | true => 
        match oResult with
        | None => Some lc
        | Some Result => 
          match (getOperandValue TD Result lc' gl) with 
          | Some gr => Some lc
          | None => None
          end
        end
    end.

Inductive dbCall : system -> TargetData -> list product -> GVMap -> 
                   GVMap -> GVMap -> list mblock -> mem -> 
                   call -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Result -> Prop :=
| dbCall_internal : forall S TD Ps lc gl fs rid noret tailc rt fv lp
                       Rid oResult tr lc' Mem Mem' als' Mem'' B' r als lc'',
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc' als' Mem' B' Rid oResult tr r ->
  free_allocas TD Mem' als' = Some Mem'' ->
  callUpdateLocals TD rt noret rid oResult lc lc' gl = Some lc'' ->
  dbCall S TD Ps fs gl lc als Mem
    (insn_call_nptr rid noret tailc rt fv lp)
    lc'' als Mem'' tr r

| dbCall_external : forall S TD Ps lc gl fs rid noret tailc fv fid 
                          lp fa rt la va Mem oresult Mem' als lc' gvs,
  (* only look up the current module for the time being, 
     do not support linkage. 
     FIXME: should add excall to trace
  *)
  lookupExFdecViaGV TD Ps gl lc fs fv = 
    Some (fdec_intro (fheader_intro fa rt fid la va)) ->
  params2GVs TD lp lc gl = Some gvs ->
  OpsemAux.callExternalFunction Mem fid gvs = 
    Some (oresult, Mem') ->
  exCallUpdateLocals TD rt noret rid oresult lc = Some lc' ->
  dbCall S TD Ps fs gl lc als Mem
    (insn_call_nptr rid noret tailc rt fv lp)
    lc' als Mem' trace_nil Rok

| dbiCall : forall S TD Ps lc1 als1 gl fs Mem1 lc2 als2 Mem2 
    tr1 lc3 Mem3 tr2 rid nr tc t v p sid id1 id2 id3 id4 id5 id6 call0 
    cst0 cst1 cst2 cs,
  call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 cst0 cst1 cst2 = 
    (call0, cs) ->
  dbCall S TD Ps fs gl lc1 als1 Mem1 call0 lc2 als1 Mem2 tr1 Rok ->
  dbCmds TD gl lc2 als1 Mem2 cs lc3 als2 Mem3 tr2 Rok ->
  dbCall S TD Ps fs gl lc1 als1 Mem1
    (insn_call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 cst0 cst1 cst2)
    lc3 als2 Mem3 (trace_app tr1 tr2) Rok

| dbiCall_abort : forall S TD Ps lc1 als1 gl fs Mem1 lc2 Mem2 
    tr1 rid nr tc t v p sid id1 id2 id3 id4 id5 id6 cst0 cst1 cst2 call0 cs,
  call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 cst0 cst1 cst2 = 
    (call0, cs) ->
  dbCall S TD Ps fs gl lc1 als1 Mem1 call0 lc2 als1 Mem2 tr1 Rabort ->
  dbCall S TD Ps fs gl lc1 als1 Mem1
    (insn_call_ptr rid nr tc t v p sid id1 id2 id3 id4 id5 id6 cst0 cst1 cst2)
    lc2 als1 Mem2 tr1 Rabort

with dbSubblock : system -> TargetData -> list product -> GVMap -> GVMap -> 
                  GVMap -> list mblock -> mem -> 
                  subblock -> 
                  GVMap -> list mblock -> mem -> 
                  trace -> Result -> Prop :=
| dbSubblock_ok : forall S TD Ps lc1 als1 gl fs Mem1 cs call0 lc2 als2 Mem2 
    tr1 lc3 als3 Mem3 tr2 r,
  dbNbranches TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr1 Rok ->
  dbCall S TD Ps fs gl lc2 als2 Mem2 call0 lc3 als3 Mem3 tr2 r ->
  dbSubblock S TD Ps fs gl lc1 als1 Mem1 (mkSB cs call0) 
             lc3 als3 Mem3 (trace_app tr1 tr2) r
| dbSubblock_abort : forall S TD Ps lc1 als1 gl fs Mem1 cs call0 lc2 als2 
    Mem2 tr1,
  dbNbranches TD gl lc1 als1 Mem1 cs lc2 als2 Mem2 tr1 Rabort ->
  dbSubblock S TD Ps fs gl lc1 als1 Mem1 (mkSB cs call0) 
             lc2 als2 Mem2 tr1 Rabort

with dbSubblocks : system -> TargetData -> list product -> GVMap -> GVMap -> 
                   GVMap -> list mblock -> mem -> 
                   list subblock -> 
                   GVMap -> list mblock -> mem -> 
                   trace -> Result -> Prop :=
| dbSubblocks_nil : forall S TD Ps lc als gl fs Mem, 
    dbSubblocks S TD Ps fs gl lc als Mem nil lc als Mem trace_nil Rok
| dbSubblocks_cons : forall S TD Ps lc1 als1 gl fs Mem1 lc2 als2 Mem2 lc3 als3 
    Mem3 sb sbs' t1 t2 r,
    dbSubblock S TD Ps fs gl lc1 als1 Mem1 sb lc2 als2 Mem2 t1 Rok ->
    dbSubblocks S TD Ps fs gl lc2 als2 Mem2 sbs' lc3 als3 Mem3 t2 r ->
    dbSubblocks S TD Ps fs gl lc1 als1 Mem1 (sb::sbs') lc3 als3 Mem3 
      (trace_app t1 t2) r

with dbBlock : system -> TargetData -> list product -> GVMap -> GVMap -> 
       fdef -> list GenericValue -> State -> State -> trace -> Result -> Prop :=
| dbBlock_ok : forall S TD Ps F tr1 tr2 l ps sbs cs tmn gl fs lc1 als1 Mem1
                         lc2 als2 Mem2 lc3 als3 Mem3 lc4 B' arg tr3,
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    sbs
    lc2 als2 Mem2
    tr1 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs lc3 als3 Mem3 tr2 Rok ->
  dbTerminator TD Mem3 F gl
    (block_common l ps sbs cs tmn) lc3
    tmn
    B' lc4
    tr3 ->
  dbBlock S TD Ps fs gl F arg
    (mkState (mkEC (block_common l ps sbs cs tmn) lc1 als1) Mem1)
    (mkState (mkEC B' lc4 als3) Mem3)
    (trace_app (trace_app tr1 tr2) tr3) Rok
| dbBlock_abort1 : forall S TD Ps F tr1 tr2 l ps sbs cs tmn gl fs lc1 als1 Mem1
                         lc2 als2 Mem2 lc3 als3 Mem3 arg,
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    sbs
    lc2 als2 Mem2
    tr1 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs lc3 als3 Mem3 tr2 Rabort ->
  dbBlock S TD Ps fs gl F arg
    (mkState (mkEC (block_common l ps sbs cs tmn) lc1 als1) Mem1)
    (mkState (mkEC (block_common l ps nil nil tmn) lc3 als3) Mem3)
    (trace_app tr1 tr2) Rabort
| dbBlock_abort2 : forall S TD Ps F tr1 l ps sbs cs tmn gl fs lc1 als1 Mem1
                         lc2 als2 Mem2 arg,
  dbSubblocks S TD Ps fs gl
    lc1 als1 Mem1
    sbs
    lc2 als2 Mem2
    tr1 Rabort ->
  dbBlock S TD Ps fs gl F arg
    (mkState (mkEC (block_common l ps sbs cs tmn) lc1 als1) Mem1)
    (mkState (mkEC (block_common l ps nil cs tmn) lc1 als1) Mem2)
    tr1 Rabort

with dbBlocks : system -> TargetData -> list product -> GVMap -> GVMap -> 
    fdef -> list GenericValue -> State -> State -> trace -> Result -> Prop :=
| dbBlocks_nil : forall S TD Ps gl fs F arg state, 
    dbBlocks S TD Ps fs gl F arg state state trace_nil Rok
| dbBlocks_cons : forall S TD Ps gl fs F arg S1 S2 S3 t1 t2 r,
    dbBlock S TD Ps fs gl F arg S1 S2 t1 Rok ->
    dbBlocks S TD Ps fs gl F arg S2 S3 t2 r ->
    dbBlocks S TD Ps fs gl F arg S1 S3 (trace_app t1 t2) r

with dbFdef : value -> typ -> params -> system -> TargetData -> list product -> 
              GVMap -> GVMap -> GVMap -> mem -> GVMap -> list mblock -> mem -> 
              block -> id -> option value -> trace -> Result -> Prop :=
| dbFdef_func : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb Result lc1 tr1 Mem Mem1 als1 lc0
                  l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 r gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC (block_common l2 ps2 sbs2 cs2 (insn_return rid rt Result))
      lc1 als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs2 lc3 als3 Mem3 tr3 r ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc3 als3 Mem3 
    (block_common l2 ps2 sbs2 cs2 (insn_return rid rt Result)) rid 
    (Some Result) (trace_app (trace_app tr1 tr2) tr3) r

| dbFdef_func_abort1 : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb Result lc1 tr1 Mem Mem1 als1 lc0
                       l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2 gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC (block_common l2 ps2 sbs2 cs2 (insn_return rid rt Result))
      lc1 als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc2 als2 Mem2 
    (block_common l2 ps2 sbs2 cs2 (insn_return rid rt Result)) rid 
    (Some Result) (trace_app tr1 tr2) Rabort

| dbFdef_func_abort2 : forall S TD Ps gl fs fv fid lp lc rid lc0
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1 B gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC B lc1 als1) Mem1)
    tr1 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc1 als1 Mem1 B rid None tr1 Rabort

| dbFdef_proc : forall S TD Ps gl fs fv fid lp lc rid lc0
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1 gvs
                       l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3 r,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC (block_common l2 ps2 sbs2 cs2 (insn_return_void rid)) lc1 
      als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs2 lc3 als3 Mem3 tr3 r ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc3 als3 Mem3 
    (block_common l2 ps2 sbs2 cs2 (insn_return_void rid)) rid None 
    (trace_app (trace_app tr1 tr2) tr3) r

| dbFdef_proc_abort1 : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1 lc0
                       l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2 gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC (block_common l2 ps2 sbs2 cs2 (insn_return_void rid)) lc1 
      als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc2 als2 Mem2
    (block_common l2 ps2 sbs2 cs2 (insn_return_void rid)) rid None 
    (trace_app tr1 tr2) Rabort

| dbFdef_proc_abort2 : forall S TD Ps gl fs fv fid lp lc rid lc0
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1 B gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC B lc1 als1) Mem1)
    tr1 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc1 als1 Mem1 B rid None tr1 Rabort

| dbFdef_iproc : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1
                       l2 ps2 sbs2 cs2 cs3 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3
                       lc4 als4 Mem4 tr4
                       sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7 mret
                       cst0 cst1 cst2 gvs lc0,
(*
  For a function that returns a pointer, Softbound translates
         ret i32* %8                                                           
  into
         %.ptr = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 0
         %.base = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 1
         store i8* %bitcast, i8** %.base
         %.bound = getelementptr { i32*, i8*, i8* }* %shadow_ret, i32 0, i32 2
         store i8* %bitcast4, i8** %.bound
         store i32* %8, i32** %.ptr
          ret void
 
  gen_iret returns %shadow_ret %.base %.base %.ptr i32* 
*)
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC 
      (block_ret_ptr l2 ps2 sbs2 cs2 
        (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
          cst0 cst1 cst2))
      lc1 als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs2 lc3 als3 Mem3 tr3 Rok ->
  ret_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7 cst0 cst1 cst2 = 
    (cs3, mret) ->
  dbCmds TD gl lc3 als3 Mem3 cs3 lc4 als4 Mem4 tr4 Rok ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc4 als4 Mem4 
    (block_ret_ptr l2 ps2 sbs2 cs2 
      (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
        cst0 cst1 cst2)
    ) rid None 
    (trace_app (trace_app (trace_app tr1 tr2) tr3) tr4) Rok

| dbFdef_iproc_abort1 : forall S TD Ps gl fs fv fid lp lc rid lc0
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1
                       l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2 lc3 als3 Mem3 tr3
                       sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
                       cst0 cst1 cst2 gvs,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC 
      (block_ret_ptr l2 ps2 sbs2 cs2 
        (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
          cst0 cst1 cst2))
      lc1 als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rok ->
  dbNbranches TD gl lc2 als2 Mem2 cs2 lc3 als3 Mem3 tr3 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc3 als3 Mem3 
    (block_ret_ptr l2 ps2 sbs2 cs2 
      (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
        cst0 cst1 cst2)
    ) rid None 
    (trace_app (trace_app tr1 tr2) tr3) Rabort

| dbFdef_iproc_abort2 : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1
                       l2 ps2 sbs2 cs2 lc2 als2 Mem2 tr2
                       sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
                       cst0 cst1 cst2 gvs lc0,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC 
      (block_ret_ptr l2 ps2 sbs2 cs2 
        (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
          cst0 cst1 cst2))
      lc1 als1) Mem1)
    tr1 Rok ->
  dbSubblocks S TD Ps fs gl lc1 als1 Mem1 sbs2 lc2 als2 Mem2 tr2 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc2 als2 Mem2 
    (block_ret_ptr l2 ps2 sbs2 cs2 
      (insn_return_ptr sid t id1 id2 id30 id31 id4 id50 id51 id60 id61 id7
        cst0 cst1 cst2)
    ) rid None 
    (trace_app tr1 tr2) Rabort

| dbFdef_iproc_abort3 : forall S TD Ps gl fs fv fid lp lc rid
                       B1 fa rt la va lb lc1 tr1 Mem Mem1 als1 B2 gvs lc0,
  lookupFdefViaGV TD Ps gl lc fs fv = 
    Some (fdef_intro (fheader_intro fa rt fid la va) lb) ->
  getEntryBlock (fdef_intro (fheader_intro fa rt fid la va) lb) = Some B1 ->
  params2GVs TD lp lc gl = Some gvs ->
  initLocals TD la gvs = Some lc0 ->
  dbBlocks S TD Ps fs gl (fdef_intro (fheader_intro fa rt fid la va) lb) 
    gvs
    (mkState (mkEC B1 lc0 nil) Mem)
    (mkState (mkEC B2 lc1 als1) Mem1)
    tr1 Rabort ->
  dbFdef fv rt lp S TD Ps lc gl fs Mem lc1 als1 Mem1 B2 rid None tr1 Rabort
.

Scheme dbCall_ind3 := Induction for dbCall Sort Prop
  with dbSubblock_ind3 := Induction for dbSubblock Sort Prop
  with dbSubblocks_ind3 := Induction for dbSubblocks Sort Prop
  with dbBlock_ind3 := Induction for dbBlock Sort Prop
  with dbBlocks_ind3 := Induction for dbBlocks Sort Prop
  with dbFdef_ind3 := Induction for dbFdef Sort Prop.

Combined Scheme sb_db_mutind from dbCall_ind3, dbSubblock_ind3,
  dbSubblocks_ind3, dbBlock_ind3, dbBlocks_ind3, dbFdef_ind3.

Tactic Notation "sb_db_mutind_cases" tactic(first) tactic(c) :=
  first;
  [ c "dbCall_internal" | c "dbCall_external" | c "dbiCall" |
    c "dbSubblock_ok" | c "dbSubblock_abort" | 
    c "dbSubblocks_nil" | c "dbSubblocks_cons" | 
    c "dbBlock_ok" | c "dbBlock_abort" | c "dbBlocks_nil" | c "dbBlocks_cons" | 
    c "dbFdef_func" | c "dbFdef_func_abort1" | c "dbFdef_func_abort2" |
    c "dbFdef_proc" | c "dbFdef_proc_abort1" | c "dbFdef_proc_abort2" | 
    c "dbFdef_iproc" | c "dbFdef_iproc_abort1" | 
    c "dbFdef_iproc_abort2" | c "dbFdef_iproc_abort3"  ].

Hint Constructors dbCall dbSubblock dbSubblocks dbBlock dbBlocks dbFdef.

End SBopsem.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
