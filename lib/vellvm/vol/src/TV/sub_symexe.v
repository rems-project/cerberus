Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import infrastructure.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import genericvalues.
Require Import trace.
Require Import alist.
Require Import typings.
Require Import CoqListFacts.
Require Import Coqlib.

Export LLVMsyntax.
Export LLVMinfra.
Export LLVMtypings.
Export LLVMgv.

(***************************************************************)
(* Syntax easy to be proved with symbolic execution. *)

Module SBSE.

(* Symbolic execution may take some functions as special cmds with a big-step.
   For example, Sofbound's metadata functions. They may not be external 
   functions.
   But we do not want to analyze them... 

   Return None if the lib call is not a lib.
*)

Inductive Result : Set :=
| Rok : Result
| Rabort : Result
.

Axiom callLib : mem -> id -> list GenericValue -> 
  option ((option GenericValue)*mem*Result).

(* Must be realized when being extracted. E.g Softbound TV should say 
     isCallLib "__loadDereferenceCheck" = true *)
Axiom isCallLib : id -> bool.

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Definition isCall (i:cmd) : bool :=
match i with
| insn_call _ _ _ _ (value_const (const_gid _ fid)) _ => negb (isCallLib fid)
| insn_call _ _ _ _ _ _ => true
| _ => false
end.

(***************************************************************)
(** LLVM.syntax -> Symexe.syntax *)

Record nbranch := mkNB
{ nbranching_cmd:cmd;
  notcall:isCall nbranching_cmd = false
}.

Record subblock := mkSB
{
  NBs : list nbranch;
  call_cmd : cmd;
  call_cmd_isCall : isCall call_cmd = true
}.

Lemma isCall_dec : forall c, 
  {isCall c = false} + {isCall c = true}.
Proof.
  destruct c; simpl; auto.
    destruct v; simpl; auto.
      destruct c0; simpl; auto.
        destruct (isCallLib i1); simpl; auto.
Qed.

Fixpoint cmds2sbs (cs:cmds) : (list subblock*list nbranch) :=
match cs with
| nil => (nil,nil)
| c::cs' =>
  match (isCall_dec c) with
  | left isnotcall => 
    match (cmds2sbs cs') with
    | (nil, nbs0) => (nil, mkNB c isnotcall::nbs0) 
    | (mkSB nbs call0 iscall0::sbs', nbs0) => 
      (mkSB (mkNB c isnotcall::nbs) call0 iscall0::sbs', nbs0) 
    end
  | right iscall => 
    match (cmds2sbs cs') with
    | (sbs, nbs0) => (mkSB nil c iscall::sbs, nbs0) 
    end
  end
end.

Fixpoint nbranchs2cmds (nbs:list nbranch) : list cmd :=
match nbs with
| nil => nil
| (mkNB c nc)::nbs' =>c::nbranchs2cmds nbs'
end.

Definition cmd2nbranch (c:cmd) : option nbranch :=
match (isCall_dec c) with 
| left H => Some (mkNB c H)
| right _ => None
end.

(* This may not work sometimes. This function creates a proof
   that a cmd is not a call, which can only be proved to eual to
   the same proof in the context by proof-irrevelance axiom. *)
Fixpoint cmds2nbranchs (cs:list cmd) : option (list nbranch) :=
match cs with
| nil => Some nil
| c::cs' =>
  match (cmd2nbranch c, cmds2nbranchs cs') with
  | (Some nb, Some nbs') => Some (nb::nbs')
  | _ => None
  end
end.

(***************************************************************)
(** symbolic terms and memories. *)
Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_fbop : fbop -> floating_point -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list_const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list_const -> sterm
| sterm_malloc : smem -> typ -> sterm -> align -> sterm
| sterm_alloca : smem -> typ -> sterm -> align -> sterm
| sterm_load : smem -> typ -> sterm -> align -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list_sz_sterm -> sterm
| sterm_trunc : truncop -> typ -> sterm -> typ -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_fcmp : fcond -> floating_point -> sterm -> sterm -> sterm
| sterm_phi : typ -> list_sterm_l -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
| sterm_lib : smem -> id -> list_sterm -> sterm
with list_sz_sterm : Set :=
| Nil_list_sz_sterm : list_sz_sterm
| Cons_list_sz_sterm : sz -> sterm -> list_sz_sterm -> list_sz_sterm
with list_sterm : Set :=
| Nil_list_sterm : list_sterm
| Cons_list_sterm : sterm -> list_sterm -> list_sterm
with list_sterm_l : Set :=
| Nil_list_sterm_l : list_sterm_l
| Cons_list_sterm_l : sterm -> l -> list_sterm_l -> list_sterm_l
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sterm -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sterm -> align -> smem
| smem_load : smem -> typ -> sterm -> align -> smem
| smem_store : smem -> typ -> sterm -> sterm -> align -> smem
| smem_lib : smem -> id -> list_sterm -> smem
with sframe : Set :=
| sframe_init : sframe
| sframe_alloca : smem -> sframe -> typ -> sterm -> align -> sframe
.

Scheme sterm_rec2 := Induction for sterm Sort Set
  with list_sz_sterm_rec2 := Induction for list_sz_sterm Sort Set
  with list_sterm_rec2 := Induction for list_sterm Sort Set
  with list_sterm_l_rec2 := Induction for list_sterm_l Sort Set
  with smem_rec2 := Induction for smem Sort Set
  with sframe_rec2 := Induction for sframe Sort Set.

Definition se_mutrec P1 P2 P3 P4 P5 P6 :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 =>
   (pair
      (pair 
           (pair 
                 (pair 
                       (pair
                          (@sterm_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)
                          (@list_sz_sterm_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32))
                       (@list_sterm_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32))
                 (@list_sterm_l_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32))
            (@smem_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32))
      (@sframe_rec2 P1 P2 P3 P4 P5 P6 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)).

Tactic Notation "se_mut_cases" tactic(first) tactic(c) :=
  first;
  [ c "sterm_val" | 
    c "sterm_bop" |
    c "sterm_fbop" |
    c "sterm_extractvalue" |
    c "sterm_insertvalue" |
    c "sterm_malloc" |
    c "sterm_alloca" |
    c "sterm_load" |
    c "sterm_gep" |
    c "sterm_trunc" |
    c "sterm_ext" |
    c "sterm_cast" |
    c "sterm_icmp" |
    c "sterm_fcmp" |
    c "sterm_phi" |
    c "sterm_select" |
    c "sterm_lib" |
    c "list_sz_sterm_nil" |
    c "list_sz_sterm_cons" |
    c "list_sterm_nil" |
    c "list_sterm_cons" |
    c "list_sterm_l_nil" |
    c "list_sterm_l_cons" |
    c "smem_init" |
    c "smem_malloc" |
    c "smem_free" |
    c "smem_alloca" |
    c "smem_load" |
    c "smem_store" |
    c "smem_lib" |
    c "sframe_init" |
    c "sframe_alloca" ].

Fixpoint map_list_sterm (A:Set) (f:sterm->A) (l0:list_sterm) {struct l0} : list A :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm h tl_ => cons (f h) (map_list_sterm A f tl_)
  end.
Implicit Arguments map_list_sterm.

Fixpoint make_list_sterm (l0:list sterm) : list_sterm :=
  match l0 with
  | nil  => Nil_list_sterm
  | cons h tl_ => Cons_list_sterm h (make_list_sterm tl_)
  end.

Fixpoint unmake_list_sterm (l0:list_sterm) :  list sterm :=
  match l0 with
  | Nil_list_sterm => nil
  | Cons_list_sterm h tl_ =>  cons h (unmake_list_sterm tl_)
  end.

Fixpoint nth_list_sterm (n:nat) (l0:list_sterm) {struct n} : option sterm :=
  match n,l0 with
  | O, Cons_list_sterm h tl_ => Some h
  | O, other => None
  | S m, Nil_list_sterm => None
  | S m, Cons_list_sterm h tl_ => nth_list_sterm m tl_
  end.
Implicit Arguments nth_list_sterm.

Fixpoint app_list_sterm (l0 m:list_sterm) {struct l0} : list_sterm :=
  match l0 with
  | Nil_list_sterm => m
  | Cons_list_sterm h tl_ => Cons_list_sterm h (app_list_sterm tl_ m)
  end.

Fixpoint map_list_sterm_l (A:Set) (f:sterm->l->A) (l0:list_sterm_l) {struct l0} : list A :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ => cons (f h0 h1) (map_list_sterm_l A f tl_)
  end.
Implicit Arguments map_list_sterm_l.

Fixpoint make_list_sterm_l (l0:list (sterm*l)) : list_sterm_l :=
  match l0 with
  | nil  => Nil_list_sterm_l
  | cons (h0,h1) tl_ => Cons_list_sterm_l h0 h1 (make_list_sterm_l tl_)
  end.

Fixpoint unmake_list_sterm_l (l0:list_sterm_l) :  list (sterm*l) :=
  match l0 with
  | Nil_list_sterm_l => nil
  | Cons_list_sterm_l h0 h1 tl_ =>  cons (h0,h1) (unmake_list_sterm_l tl_)
  end.

Fixpoint nth_list_sterm_l (n:nat) (l0:list_sterm_l) {struct n} : option (sterm*l) :=
  match n,l0 with
  | O, Cons_list_sterm_l h0 h1 tl_ => Some (h0,h1)
  | O, other => None
  | S m, Nil_list_sterm_l => None
  | S m, Cons_list_sterm_l h0 h1 tl_ => nth_list_sterm_l m tl_
  end.
Implicit Arguments nth_list_sterm_l.

Fixpoint app_list_sterm_l (l0 m:list_sterm_l) {struct l0} : list_sterm_l :=
  match l0 with
  | Nil_list_sterm_l => m
  | Cons_list_sterm_l h0 h1 tl_ => Cons_list_sterm_l h0 h1 (app_list_sterm_l tl_ m)
  end.

Fixpoint map_list_sz_sterm (A:Set) (f:sz->sterm->A) (l0:list_sz_sterm) 
  {struct l0} : list A :=
  match l0 with
  | Nil_list_sz_sterm => nil
  | Cons_list_sz_sterm s h tl_ => cons (f s h) (map_list_sz_sterm A f tl_)
  end.
Implicit Arguments map_list_sz_sterm.

Fixpoint make_list_sz_sterm (l0:list (sz * sterm)) : list_sz_sterm :=
  match l0 with
  | nil  => Nil_list_sz_sterm
  | cons (s, h) tl_ => Cons_list_sz_sterm s h (make_list_sz_sterm tl_)
  end.

Fixpoint unmake_list_sz_sterm (l0:list_sz_sterm) :  list (sz * sterm) :=
  match l0 with
  | Nil_list_sz_sterm => nil
  | Cons_list_sz_sterm s h tl_ =>  cons (s, h) (unmake_list_sz_sterm tl_)
  end.

Fixpoint nth_list_sz_sterm (n:nat) (l0:list_sz_sterm) {struct n} 
  : option (sz * sterm) :=
  match n,l0 with
  | O, Cons_list_sz_sterm s h tl_ => Some (s, h)
  | O, other => None
  | S m, Nil_list_sz_sterm => None
  | S m, Cons_list_sz_sterm _ _ tl_ => nth_list_sz_sterm m tl_
  end.
Implicit Arguments nth_list_sz_sterm.

Fixpoint app_list_sz_sterm (l0 m:list_sz_sterm) {struct l0} : list_sz_sterm :=
  match l0 with
  | Nil_list_sz_sterm => m
  | Cons_list_sz_sterm s h tl_ => 
      Cons_list_sz_sterm s h (app_list_sz_sterm tl_ m)
  end.

Inductive sterminator : Set :=
| stmn_return : id -> typ -> sterm -> sterminator
| stmn_return_void : id -> sterminator
| stmn_br : id -> sterm -> l -> l -> sterminator
| stmn_br_uncond : id -> l -> sterminator
| stmn_unreachable : id -> sterminator
.

Inductive scall : Set :=
(* FIXME: the value should be a sterm!!! *)
| stmn_call : 
    id -> noret -> clattrs -> typ -> value -> list (typ*attributes*sterm) ->
      scall
.

Definition smap := list (atom*sterm).

Record sstate : Set := mkSstate 
{
  STerms : smap;
  SMem : smem;
  SFrame : sframe;
  SEffects : list sterm
}.

Definition sstate_init := mkSstate nil smem_init sframe_init nil.

Fixpoint lookupSmap (sm:smap) (i0:id) : sterm :=
match sm with
| nil => (sterm_val (value_id i0))
| (id0, s0)::sm' => 
  if i0 == id0 then s0 else lookupSmap sm' i0
end.

Definition value2Sterm (sm:smap) (v:value) : sterm :=
match v with
| value_const _ => sterm_val v
| value_id i0 => lookupSmap sm i0
end.

Fixpoint list_param__list_typ_subst_sterm (list_param1:params) (sm:smap) 
  : list (typ*attributes*sterm) :=
match list_param1 with
| nil => nil
| (t, attr, v)::list_param1' => 
    (t, attr, (value2Sterm sm v))::
      (list_param__list_typ_subst_sterm list_param1' sm)
end.

Inductive list_value : Set := 
 | Nil_list_value : list_value
 | Cons_list_value : value -> list_value -> list_value.

Fixpoint map_list_value (A:Set) (f:value->A) (l0:list_value) {struct l0} : list A :=
  match l0 with
  | Nil_list_value => nil
  | Cons_list_value h tl_ => cons (f h) (map_list_value A f tl_)
  end.
Implicit Arguments map_list_value.

Fixpoint make_list_value (l0:list value) : list_value :=
  match l0 with
  | nil  => Nil_list_value
  | cons h tl_ => Cons_list_value h (make_list_value tl_)
  end.

Fixpoint unmake_list_value (l0:list_value) :  list value :=
  match l0 with
  | Nil_list_value => nil
  | Cons_list_value h tl_ =>  cons h (unmake_list_value tl_)
  end.

Fixpoint nth_list_value (n:nat) (l0:list_value) {struct n} : option value :=
  match n,l0 with
  | O, Cons_list_value h tl_ => Some h 
  | O, other => None
  | S m, Nil_list_value => None
  | S m, Cons_list_value h tl_ => nth_list_value m tl_
  end.
Implicit Arguments nth_list_value.

Fixpoint app_list_value (l0 m:list_value) {struct l0} : list_value :=
  match l0 with
  | Nil_list_value => m
  | Cons_list_value h tl_ => Cons_list_value h (app_list_value tl_ m)
  end.

Definition se_lib : forall i id0 noret0 tailc0 ft fv lp (st:sstate),
  i=insn_call id0 noret0 tailc0 ft fv lp ->
  isCall i = false ->
  sstate.
Proof.
  intros; subst. simpl in H0.
  destruct fv; try solve [inversion H0].
  destruct c; try solve [inversion H0].
  apply
    (mkSstate (updateAddAL _ st.(STerms) id0 
                (sterm_lib st.(SMem) i0
                  (make_list_sterm 
                    (map_list_value 
                      (value2Sterm st.(STerms))
                      (make_list_value (snd (List.split lp)))
                    ))))
              (smem_lib st.(SMem) i0 
                (make_list_sterm 
                  (map_list_value 
                    (value2Sterm st.(STerms)) 
                    (make_list_value (snd (List.split lp)))
                  )))
              st.(SFrame)
              st.(SEffects)).
Defined.

Definition se_cmd (st : sstate) (c:nbranch) : sstate :=
match c with 
| mkNB i notcall =>
  (match i as r return (i = r -> _) with 
  | insn_bop id0 op0 sz0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_bop op0 sz0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fbop id0 op0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fbop op0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
 | insn_extractvalue id0 t1 v1 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_extractvalue t1 
                     (value2Sterm st.(STerms) v1)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_insertvalue id0 t1 v1 t2 v2 cs3 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_insertvalue 
                     t1 
                     (value2Sterm st.(STerms) v1)
                     t2 
                     (value2Sterm st.(STerms) v2)
                     cs3))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_malloc id0 t1 v1 al1 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_malloc st.(SMem) t1 (value2Sterm st.(STerms) v1) al1))
                 (smem_malloc st.(SMem) t1 (value2Sterm st.(STerms) v1) al1)
                 st.(SFrame)
                 st.(SEffects))
  | insn_free id0 t0 v0 => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_free st.(SMem) t0 
                   (value2Sterm st.(STerms) v0))
                 st.(SFrame)
                 st.(SEffects))
  | insn_alloca id0 t1 v1 al1 => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_alloca st.(SMem) t1 (value2Sterm st.(STerms) v1) al1))
                 (smem_alloca st.(SMem) t1 (value2Sterm st.(STerms) v1) al1)
                 (sframe_alloca st.(SMem) st.(SFrame) t1 (value2Sterm st.(STerms) v1) al1)
                 st.(SEffects))
  | insn_load id0 t2 v2 align => fun _ =>   
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_load st.(SMem) t2 
                     (value2Sterm st.(STerms) v2) align))
                 (smem_load st.(SMem) t2 
                   (value2Sterm st.(STerms) v2) align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_store id0 t0 v1 v2 align => fun _ =>  
       (mkSstate st.(STerms)
                 (smem_store st.(SMem) t0 
                   (value2Sterm st.(STerms) v1)
                   (value2Sterm st.(STerms) v2)
                   align)
                 st.(SFrame)
                 st.(SEffects))
  | insn_gep id0 inbounds0 t1 v1 lv2 => fun _ =>  
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_gep inbounds0 t1 
                     (value2Sterm st.(STerms) v1)
                     (make_list_sz_sterm 
                       (map_list_sz_value 
                         (fun sz' v' => (sz', value2Sterm st.(STerms) v'))
                          lv2))))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_trunc id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_trunc op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_ext id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_ext op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_cast id0 op0 t1 v1 t2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_cast op0 t1 
                     (value2Sterm st.(STerms) v1)
                     t2))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_icmp id0 c0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_icmp c0 t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_fcmp id0 c0 fp0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_fcmp c0 fp0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_select id0 v0 t0 v1 v2 => fun _ => 
       (mkSstate (updateAddAL _ st.(STerms) id0 
                   (sterm_select 
                     (value2Sterm st.(STerms) v0)
                     t0 
                     (value2Sterm st.(STerms) v1)
                     (value2Sterm st.(STerms) v2)))
                 st.(SMem)
                 st.(SFrame)
                 st.(SEffects))
  | insn_call id0 noret0 tailc0 ft fv lp =>
    fun (EQ:i=insn_call id0 noret0 tailc0 ft fv lp ) =>
    se_lib i id0 noret0 tailc0 ft fv lp st EQ notcall
  end) (@refl_equal _ i)
end.

Fixpoint _se_phinodes (st st0: sstate) (ps:list phinode) : sstate :=
match ps with
| nil => st
| insn_phi id0 t0 idls0::ps' =>  
    _se_phinodes 
     (mkSstate (updateAL _ st.(STerms) id0 
                 (sterm_phi 
                   t0 
                   (make_list_sterm_l
                     (map_list_value_l
                       (fun v5 l5 =>
                        ((value2Sterm st.(STerms) v5), l5)
                       )
                       idls0
                     )
                   )
                 )
               )
               st.(SMem)
               st.(SFrame)
               st.(SEffects))
     st0
     ps'
end.

Fixpoint se_phinodes (st: sstate) (ps:list phinode) := _se_phinodes st st ps.

Fixpoint se_cmds (st : sstate) (cs:list nbranch) : sstate :=
match cs with
| nil => st
| c::cs' => se_cmds (se_cmd st c) cs'
end.

Definition se_terminator (st : sstate) (i:terminator) : sterminator :=
match i with 
| insn_return id0 t0 v0 => stmn_return id0 t0 (value2Sterm st.(STerms) v0)
| insn_return_void id0 => stmn_return_void id0 
| insn_br id0 v0 l1 l2 => stmn_br id0 (value2Sterm st.(STerms) v0) l1 l2
| insn_br_uncond id0 l0 => stmn_br_uncond id0 l0
| insn_unreachable id0 => stmn_unreachable id0 
end.

Definition se_call : forall (st : sstate) (i:cmd) (iscall:isCall i = true), scall.
Proof.
  intros. unfold isCall in iscall.
  destruct i0; try solve [inversion iscall].
  apply (@stmn_call i0 n c t v 
                      (list_param__list_typ_subst_sterm p st.(STerms))).
Defined.

(* Definions below have not been used yet. *)

Fixpoint subst_tt (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if id0 == id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fbop op fp s1 s2 => 
    sterm_fbop op fp (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_tt id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_tt id0 s0 s1) t2 (subst_tt id0 s0 s2) cs
| sterm_malloc m1 t1 s1 align => 
    sterm_malloc (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_alloca m1 t1 s1 align => 
    sterm_alloca (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_load m1 t1 s1 align => 
    sterm_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_tt id0 s0 s1) (subst_tlzt id0 s0 ls2)
| sterm_trunc truncop t1 s1 t2 => 
    sterm_trunc truncop t1 (subst_tt id0 s0 s1) t2
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_tt id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_tt id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_fcmp cond fp1 s1 s2 => 
    sterm_fcmp cond fp1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (subst_tltl id0 s0 lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_tt id0 s0 s1) t1 (subst_tt id0 s0 s2) (subst_tt id0 s0 s3)
| sterm_lib m id ls => sterm_lib (subst_tm id0 s0 m) id (subst_tlt id0 s0 ls)
end
with subst_tlzt (id0:id) (s0:sterm) (ls:list_sz_sterm) : list_sz_sterm :=
match ls with
| Nil_list_sz_sterm => Nil_list_sz_sterm
| Cons_list_sz_sterm sz0 s ls' => 
    Cons_list_sz_sterm sz0 (subst_tt id0 s0 s) (subst_tlzt id0 s0 ls')
end
with subst_tlt (id0:id) (s0:sterm) (ls:list_sterm) : list_sterm :=
match ls with
| Nil_list_sterm => Nil_list_sterm
| Cons_list_sterm s ls' => Cons_list_sterm (subst_tt id0 s0 s) (subst_tlt id0 s0 ls')
end
with subst_tltl (id0:id) (s0:sterm) (ls:list_sterm_l) : list_sterm_l :=
match ls with
| Nil_list_sterm_l => Nil_list_sterm_l
| Cons_list_sterm_l s l0 ls' => Cons_list_sterm_l (subst_tt id0 s0 s) l0 (subst_tltl id0 s0 ls')
end
with subst_tm (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_tm id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_tm id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 align => smem_load (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) align 
| smem_store m1 t1 s1 s2 align => smem_store (subst_tm id0 s0 m1) t1 (subst_tt id0 s0 s1) (subst_tt id0 s0 s2) align
| smem_lib m id ls => smem_lib (subst_tm id0 s0 m) id (subst_tlt id0 s0 ls)
end
.

Fixpoint subst_mt (sm:smap) (s:sterm) : sterm :=
match sm with
| nil => s
| (id0, s0)::sm' => subst_mt sm' (subst_tt id0 s0 s)
end.

Fixpoint subst_mm (sm:smap) (m:smem) : smem :=
match sm with
| nil => m
| (id0, s0)::sm' => subst_mm sm' (subst_tm id0 s0 m)
end.

Definition sterm_dec_prop (st1:sterm) := forall st2, {st1=st2} + {~st1=st2}.
Definition list_sz_sterm_dec_prop (stls1:list_sz_sterm) 
  := forall stls2, {stls1=stls2} + {~stls1=stls2}.
Definition list_sterm_dec_prop (sts1:list_sterm) := forall sts2, {sts1=sts2} + {~sts1=sts2}.
Definition list_sterm_l_dec_prop (stls1:list_sterm_l) := forall stls2, {stls1=stls2} + {~stls1=stls2}.
Definition smem_dec_prop (sm1:smem) := forall sm2, {sm1=sm2} + {~sm1=sm2}.
Definition sframe_dec_prop (sf1:sframe) := forall sf2, {sf1=sf2} + {~sf1=sf2}.

Lemma se_dec :
  (forall st1, sterm_dec_prop st1) *
  (forall sts1, list_sz_sterm_dec_prop sts1) *
  (forall sts1, list_sterm_dec_prop sts1) *
  (forall stls1, list_sterm_l_dec_prop stls1) *
  (forall sm1, smem_dec_prop sm1) *
  (forall sf1, sframe_dec_prop sf1).
Proof.
  (se_mut_cases (apply se_mutrec) Case); 
    unfold sterm_dec_prop, list_sz_sterm_dec_prop, list_sterm_dec_prop, 
           list_sterm_l_dec_prop, smem_dec_prop, sframe_dec_prop;
    intros.
  Case "sterm_val".
    destruct st2; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "sterm_bop".
    destruct st2; try solve [done_right].
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@Size.dec s s2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_fbop".
    destruct st2; try solve [done_right].
    destruct (@fbop_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_extractvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_insertvalue".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "sterm_malloc".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "sterm_alloca".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "sterm_load".    
    destruct st2; try solve [done_right].
    destruct (@H s1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 st2); subst; try solve [auto | done_right].
  Case "sterm_gep".    
    destruct st2; try solve [done_right].
    destruct (@bool_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@H0 l1); subst; try solve [auto | done_right].
  Case "sterm_trunc".
    destruct st2; try solve [done_right].
    destruct (@truncop_dec t t2); subst; try solve [done_right].
    destruct (@typ_dec t0 t3); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t1 t4); subst; try solve [auto | done_right].
  Case "sterm_ext".
    destruct st2; try solve [done_right].
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_cast".
    destruct st2; try solve [done_right].
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@H st2); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "sterm_icmp".
    destruct st2; try solve [done_right].
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_fcmp".
    destruct st2; try solve [done_right].
    destruct (@fcond_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [auto | done_right].
  Case "sterm_phi".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H l1); subst; try solve [auto | done_right].
  Case "sterm_select".
    destruct st2; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H st2_1); subst; try solve [done_right].
    destruct (@H0 st2_2); subst; try solve [done_right].
    destruct (@H1 st2_3); subst; try solve [auto | done_right].
  Case "sterm_lib".
    destruct st2; try solve [done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@H0 l1); subst; try solve [auto | done_right].    
  Case "list_sz_sterm_nil".
    destruct stls2; subst; try solve [auto | done_right].
  Case "list_sz_sterm_cons".
    destruct stls2; subst; try solve [auto | done_right].
    destruct (@Size.dec s s1); subst; try solve [done_right].
    destruct (@H s2); subst; try solve [done_right].
    destruct (@H0 stls2); subst; try solve [auto | done_right].
  Case "list_sterm_nil".
    destruct sts2; subst; try solve [auto | done_right].
  Case "list_sterm_cons".
    destruct sts2; subst; try solve [auto | done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@H0 sts2); subst; try solve [auto | done_right].
  Case "list_sterm_l_nil".
    destruct stls2; subst; try solve [auto | done_right].
  Case "list_sterm_l_cons".
    destruct stls2; subst; try solve [auto | done_right].
    destruct (@H s0); subst; try solve [done_right].
    destruct (@l_dec l0 l2); subst; try solve [done_right].
    destruct (@H0 stls2); subst; try solve [auto | done_right].
  Case "smem_init".
    destruct sm2; subst; try solve [auto | done_right].
  Case "smem_malloc".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "smem_free".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_alloca".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "smem_load".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 s1); subst; try solve [auto | done_right].
  Case "smem_store".
    destruct sm2; subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@H0 s2); subst; try solve [auto | done_right].
    destruct (@H1 s3); subst; try solve [auto | done_right].
  Case "smem_lib".
    destruct sm2; try solve [done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct (@H sm2); subst; try solve [done_right].
    destruct (@H0 l1); subst; try solve [auto | done_right].    
  Case "sframe_init".
    destruct sf2; subst; try solve [auto | done_right].
  Case "sframe_alloca".
    destruct sf2; subst; try solve [done_right].
    destruct (@H s2); subst; try solve [done_right].
    destruct (@H0 sf2); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@H1 s3); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
Qed.

Lemma sterm_dec : forall (st1 st2:sterm), {st1=st2} + {~st1=st2}.
destruct se_dec as [[[[[H _] _] _] _] _]. auto.
Qed.

Lemma list_sz_sterm_dec :  forall (ts1 ts2:list_sz_sterm), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[[[_ H] _] _] _] _]. auto.
Qed. 

Lemma list_sterm_dec :  forall (ts1 ts2:list_sterm), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[[_ H] _] _] _]. auto.
Qed. 

Lemma list_sterm_l_dec :  forall (ts1 ts2:list_sterm_l), {ts1=ts2}+{~ts1=ts2}.
destruct se_dec as [[[_ H] _] _]. auto.
Qed. 

Lemma smem_dec : forall (sm1 sm2:smem), {sm1=sm2} + {~sm1=sm2}.
destruct se_dec as [[_ H] _]. auto.
Qed.

Lemma sframe_dec : forall (sf1 sf2:sframe), {sf1=sf2} + {~sf1=sf2}.
destruct se_dec as [_ H]. auto.
Qed.

Lemma sterminator_dec : forall (st1 st2:sterminator), {st1=st2} + {~st1=st2}.
Proof.
  decide equality.
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma list_typ_attributes_sterm_dec : 
  forall (l1 l2:list (typ*attributes*sterm)), {l1=l2}+{~l1=l2}.
Proof.
  decide equality.
    destruct a as [ [t a] s]. destruct p as [ [t0 a0] s0].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@attributes_dec a a0); subst; try solve [done_right].
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma scall_dec : forall (sc1 sc2:scall), {sc1=sc2} + {~sc1=sc2}.
Proof.
  decide equality.
    destruct (@list_typ_attributes_sterm_dec l0 l1); 
      subst; try solve [auto | done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].

    destruct c. destruct c0.
    destruct (@bool_dec t1 t2); subst; try solve [auto | done_right].
    destruct (@callconv_dec c c0); subst; try solve [auto | done_right].
    destruct (@attributes_dec a a1); subst; try solve [auto | done_right].
    destruct (@attributes_dec a0 a2); subst; try solve [auto | done_right].

    destruct (@bool_dec n n0); subst; try solve [auto | done_right].
Qed.

Lemma smap_dec : forall (sm1 sm2:smap), {sm1=sm2}+{~sm1=sm2}.
Proof.
  decide equality.
    destruct a. destruct p.
    destruct (@id_dec a a0); subst; try solve [done_right]. 
    destruct (@sterm_dec s s0); subst; try solve [auto | done_right].
Qed.

Lemma sterms_dec :  forall (ts1 ts2:list sterm), {ts1=ts2}+{~ts1=ts2}.
Proof.
  decide equality.
    destruct (@sterm_dec a s); subst; try solve [auto | done_right].
Qed.

Lemma sstate_dec : forall (sts1 sts2:sstate), {sts1=sts2} + {~sts1=sts2}.
Proof.
  decide equality.
    destruct (@sterms_dec SEffects0 SEffects1); subst; try solve [auto | done_right].
    destruct (@sframe_dec SFrame0 SFrame1); subst; try solve [auto | done_right].
    destruct (@smem_dec SMem0 SMem1); subst; try solve [auto | done_right].
    destruct (@smap_dec STerms0 STerms1); subst; try solve [auto | done_right].
Qed.

End SBSE.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
