Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import List.
Require Import Arith.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import alist.
Require Import syntax.
Require Import infrastructure.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import ZArith.

Module VMgv.

Import VMsyntax.
Import VMinfra.

Definition GenericValue := int32.
Definition GVMap := list (id*GenericValue).

Definition GV2int (gv:GenericValue) : Z := Int.signed 31 gv.

Definition isGVZero (gv:GenericValue) : bool :=
match (GV2int gv) with
| z => if Coqlib.zeq z 0 then true else false
end.

Definition mbop (op:bop) (gv1 gv2:GenericValue) : GenericValue :=
match op with
| bop_add => Int.add 31 gv1 gv2
| bop_sub => Int.sub 31 gv1 gv2
| bop_mul => Int.mul 31 gv1 gv2
| bop_udiv => Int.divu 31 gv1 gv2
| bop_sdiv => Int.divs 31 gv1 gv2
| bop_urem => Int.modu 31 gv1 gv2
| bop_srem => Int.mods 31 gv1 gv2
| bop_shl => Int.shl 31 gv1 gv2
| bop_lshr => Int.shrx 31 gv1 gv2
| bop_ashr => Int.shr 31 gv1 gv2
| bop_and => Int.and 31 gv1 gv2
| bop_or => Int.or 31 gv1 gv2
| bop_xor => Int.xor 31 gv1 gv2
end.

Definition of_bool (b: bool) : int32 :=
if b then Int.one 31 else Int.zero 31.

Definition micmp (c:cond) (gv1 gv2:GenericValue) : GenericValue :=
of_bool
  (match c with
  | cond_eq => Int.cmp 31 Ceq gv1 gv2
  | cond_ne => Int.cmp 31 Cne gv1 gv2
  | cond_ugt => Int.cmpu 31 Cgt gv1 gv2
  | cond_uge => Int.cmpu 31 Cge gv1 gv2
  | cond_ult => Int.cmpu 31 Clt gv1 gv2
  | cond_ule => Int.cmpu 31 Cle gv1 gv2
  | cond_sgt => Int.cmp 31 Cgt gv1 gv2
  | cond_sge => Int.cmp 31 Cge gv1 gv2
  | cond_slt => Int.cmp 31 Clt gv1 gv2
  | cond_sle => Int.cmp 31 Cle gv1 gv2
  end).

(**************************************)
(** Convert const to GV. *)

Definition const2GV (c:const) : GenericValue := 
match c with
| const_int n => Int.repr 31 (INTEGER.to_Z n)
end.

Definition getOperandValue (v:value) (locals:GVMap) : option GenericValue := 
match v with
| value_id id => lookupAL _ locals id 
| value_const c => Some (const2GV c)
end.

(**************************************)
(* helper functions *)

Definition BOP (lc:GVMap) (op:bop) (v1 v2:value) : option GenericValue :=
match (getOperandValue v1 lc, getOperandValue v2 lc) with
| (Some gv1, Some gv2) => Some (mbop op gv1 gv2)
| _ => None
end
.

Definition ICMP (lc:GVMap) (c:cond) (v1 v2:value) : option GenericValue :=
match (getOperandValue v1 lc, getOperandValue v2 lc) with
| (Some gv1, Some gv2) => Some (micmp c gv1 gv2)
| _ => None
end.

(********** properties *******************)

Ltac inv H := inversion H; subst; clear H.

Ltac tinv H := try solve [inversion H].

Lemma BOP_inversion : forall lc b v1 v2 gv,
  BOP lc b v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue v1 lc = Some gv1 /\
    getOperandValue v2 lc = Some gv2 /\
    mbop b gv1 gv2 = gv.
Proof.
  intros lc b v1 v2 gv HBOP.
  unfold BOP in HBOP.
  remember (getOperandValue v1 lc) as ogv1.
  destruct ogv1; try solve [inversion HBOP].
    remember (getOperandValue v2 lc) as ogv2.
    destruct ogv2; try solve [inversion HBOP].
    inversion HBOP; subst.
    exists g. exists g0. auto.
Qed.

Lemma ICMP_inversion : forall lc cond v1 v2 gv,
  ICMP lc cond v1 v2 = Some gv ->
  exists gv1, exists gv2,
    getOperandValue v1 lc = Some gv1 /\
    getOperandValue v2 lc = Some gv2 /\
    micmp cond gv1 gv2 = gv.
Proof.
  intros lc cond0 v1 v2 gv HICMP.
  unfold ICMP in HICMP.
  remember (getOperandValue v1 lc) as ogv1.
  destruct ogv1; try solve [inversion HICMP].
    remember (getOperandValue v2 lc) as ogv2.
    destruct ogv2; try solve [inversion HICMP].
    inversion HICMP; subst.
    exists g. exists g0. auto.
Qed.

Lemma getOperandValue_eqAL : forall lc1 lc2 v,
  eqAL _ lc1 lc2 ->
  getOperandValue v lc1 = getOperandValue v lc2.
Proof.
  intros lc1 lc2 v HeqAL.
  unfold getOperandValue in *.
  destruct v; auto.
Qed.

Lemma BOP_eqAL : forall lc1 lc2 bop0 v1 v2,
  eqAL _ lc1 lc2 ->
  BOP lc1 bop0 v1 v2 = BOP lc2 bop0 v1 v2.
Proof.
  intros lc1 lc2 bop0 v1 v2 HeqEnv.
  unfold BOP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

Lemma ICMP_eqAL : forall lc1 lc2 cond v1 v2,
  eqAL _ lc1 lc2 ->
  ICMP lc1 cond v1 v2 = ICMP lc2 cond v1 v2.
Proof.
  intros lc1 lc2 cond0 v1 v2 HeqAL.
  unfold ICMP in *.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v1); auto.
  rewrite getOperandValue_eqAL with (lc2:=lc2)(v:=v2); auto.
Qed.

End VMgv.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
