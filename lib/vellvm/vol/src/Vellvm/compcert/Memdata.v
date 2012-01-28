(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Znumtheory.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition Mint32 := Mint 31.

Definition bytesize_chunk (wz:nat) := ZRdiv (Z_of_nat (S wz)) 8.
Definition bytesize_chunk_nat (wz:nat) := nat_of_Z (bytesize_chunk wz).

Lemma bytesize_chunk_pos:
  forall wz, bytesize_chunk wz > 0.
Proof.
  intros. unfold bytesize_chunk.
  apply ZRdiv_prop5.
Qed.

Lemma bytesize_chunk_conv:
  forall wz, bytesize_chunk wz = Z_of_nat (bytesize_chunk_nat wz).
Proof.
  intros.
  unfold bytesize_chunk, bytesize_chunk_nat, bytesize_chunk.
  decEq. 
  rewrite nat_of_Z_eq. auto.
    apply ZRdiv_prop2; auto with zarith.
Qed.

Lemma bytesize_chunk_nat_pos:
  forall wz, exists n, bytesize_chunk_nat wz = S n.
Proof.
  intros. 
  generalize (bytesize_chunk_pos wz). rewrite bytesize_chunk_conv. 
  destruct (bytesize_chunk_nat wz).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint wz => bytesize_chunk wz
  | Mfloat32 => 4
  | Mfloat64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; try solve [omega | apply bytesize_chunk_pos].
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; try solve [reflexivity | apply bytesize_chunk_conv].
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

Lemma size_chunk_nat_pos':
  forall chunk, (size_chunk_nat chunk > 0)%nat.
Proof.
  intros.
  destruct (@size_chunk_nat_pos chunk) as [n J].
  rewrite J. omega.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. the PowerPC) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC and ARM. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint wz => 
    if le_lt_dec wz 31
    then bytesize_chunk wz
    else if zeq (bytesize_chunk wz) 8 then 4 else 1
  | _ => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; try omega.
    destruct (le_lt_dec n 31); try omega.
      apply bytesize_chunk_pos.
      destruct (zeq (bytesize_chunk n) 8); omega.
Qed.

Lemma bytesize_chunk_7_eq_1 : bytesize_chunk 7 = 1.
Proof. compute. auto. Qed.

Lemma bytesize_chunk_31_eq_4 : bytesize_chunk 31 = 4.
Proof. compute. auto. Qed.

Lemma bytesize_chunk_63_eq_8 : bytesize_chunk 63 = 8.
Proof. compute. auto. Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try solve [
    apply Zdivide_refl |
    destruct (le_lt_dec n 31); auto with zarith |
    exists 2; auto ]. 

    destruct (le_lt_dec n 31); auto with zarith.
    destruct (zeq (bytesize_chunk n) 8); auto with zarith.
      rewrite e.
      assert (8 = 2 * 4) as EQ. auto with zarith.
      rewrite EQ.
      apply Zdivide_factor_l.
Qed.

Lemma bytesize_chunk_le : forall n m,
  (m <= n)%nat ->
  bytesize_chunk m <= bytesize_chunk n.  
Proof.
  intros n m H.
  unfold bytesize_chunk, ZRdiv.
  simpl.
  assert (Zpos (P_of_succ_nat m) <= Zpos (P_of_succ_nat n)) as A.
    apply Zpos_P_of_succ_nat_mono; auto.

  remember (Zpos (P_of_succ_nat m)) as z1.
  remember (Zpos (P_of_succ_nat n)) as z2.
  assert (z1 > 0) as C. rewrite Heqz1. auto with zarith.
  clear - A C.
  assert (z1 / 8 <= z2 / 8) as B.
    apply Z_div_le; auto with zarith.
  destruct (zeq (z1 mod 8) 0).
    destruct (zeq (z2 mod 8) 0); auto with zarith.
    destruct (zeq (z2 mod 8) 0); auto with zarith.
      assert (z1 = 8*(z1/8) + (z1 mod 8)) as Z1.
        apply Z_div_mod_eq; auto with zarith.
      assert (z2 = 8*(z2/8) + (z2 mod 8)) as Z2.
        apply Z_div_mod_eq; auto with zarith.
      rewrite e in Z2.
      assert (0 <= z1 mod 8 < 8) as D.
        apply Z_mod_lt; auto with zarith.
      destruct (Z_le_dec (z1 / 8 + 1) (z2 / 8)); auto.
        contradict A.
        rewrite Z1. rewrite Z2.
        clear Z1 Z2 e. auto with zarith.
Qed.
 
Lemma bytesize_chunk_le_31 : forall n,
  (n <= 31)%nat -> bytesize_chunk n <= 4.
Proof.
  intros. 
  rewrite <- bytesize_chunk_31_eq_4.
  apply bytesize_chunk_le; auto.
Qed.

Lemma bytesize_chunk_32_eq_5 : bytesize_chunk 32 = 5.
Proof. compute. auto. Qed.

Lemma bytesize_chunk_gt_31 : forall n,
  (31 < n)%nat -> bytesize_chunk n > 4.
Proof.
  intros. 
  assert ((32 <= n)%nat) as J. auto with zarith.
  apply bytesize_chunk_le in J.
  rewrite bytesize_chunk_32_eq_5 in J.
  auto with zarith.
Qed.

Lemma bytesize_chunk_31_neq : forall n1 n2,
  (n1 <= 31 < n2)%nat ->
  bytesize_chunk n1 <> bytesize_chunk n2.
Proof.
  intros.
  destruct H.
  apply bytesize_chunk_le_31 in H.
  apply bytesize_chunk_gt_31 in H0.
  omega.
Qed.

Lemma bytesize_chunk_31_neq' : forall n1 n2,
  (n1 <= 31 < n2)%nat ->
  bytesize_chunk n2 <> bytesize_chunk n1.
Proof.
  intros.
  destruct H.
  apply bytesize_chunk_le_31 in H.
  apply bytesize_chunk_gt_31 in H0.
  omega.
Qed.

Lemma bytesize_chunk_neq : forall n1 n2,
  (n1 <= 31)%nat -> (n2 > 31)%nat ->
  bytesize_chunk n1 <> bytesize_chunk n2.
Proof.
  intros.
  apply bytesize_chunk_le_31 in H.
  apply bytesize_chunk_gt_31 in H0.
  omega.
Qed.

Lemma align_chunk_compat:
  forall chunk1 chunk2,
  size_chunk chunk1 = size_chunk chunk2 -> 
  align_chunk chunk1 = align_chunk chunk2.
Proof.
  intros chunk1 chunk2. 
  destruct chunk1; destruct chunk2; simpl; try congruence; auto.
    destruct (le_lt_dec n 31); auto.
      destruct (le_lt_dec n0 31); auto.
        intro. contradict H; auto using bytesize_chunk_31_neq.
      destruct (le_lt_dec n0 31); auto.
        intro. contradict H; auto using bytesize_chunk_31_neq'.

    intro J.
    destruct (zeq (bytesize_chunk n) 8); auto.
      destruct (zeq (bytesize_chunk n0) 8); auto.
        rewrite e in J. rewrite J in n1. contradict n1; auto.
      destruct (zeq (bytesize_chunk n0) 8); auto.
        rewrite e in J. rewrite J in n1. contradict n1; auto.

    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_gt_31 in l.
      intro. rewrite H in l. contradict l; omega.

    intro J. rewrite J.
    destruct (zeq 8 8) as [ | n']; try solve [contradict n'; auto].
    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_le_31 in l.
      rewrite J in l. contradict l. omega.

    intro J. rewrite <- J.
    destruct (zeq 4 8) as [e' | ]; try solve [inversion e'].
    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_gt_31 in l.
      rewrite J in l. contradict l. omega.

    intro J. rewrite <- J.
    destruct (zeq 8 8) as [ | n']; try solve [contradict n'; auto].
    destruct (le_lt_dec n 31); auto.
      apply bytesize_chunk_le_31 in l.
      rewrite <- J in l. contradict l. omega.
Qed.

Definition chunk_eq (c1 c2:memory_chunk) : Prop :=
  size_chunk c1 = size_chunk c2 /\
  match c1, c2 with
  | Mint wz1, Mint wz2 => wz1 = wz2
  | _, _ => True
  end.

Lemma chunk_eq_refl : forall c, chunk_eq c c.
Proof.
  destruct c; split; auto.
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque pointer;
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: nat -> byte -> memval
  | Pointer: block -> int32 -> nat -> memval
  | IPointer : int32 -> nat -> memval.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  according to a given memory chunk. *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Int.repr 7 x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Int.unsigned 7 b + int_of_bytes l' * 256
  end.

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.


Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma int_of_bytes_of_int_wz:
  forall n wz x,
  0 < Z_of_nat n ->
  Int.repr wz (int_of_bytes (bytes_of_int n (Int.unsigned wz x))) = 
  Int.zero_ext wz (Z_of_nat n * 8) x.
Proof.
  intros. rewrite int_of_bytes_of_int. 
  rewrite <- (Int.repr_unsigned wz (Int.zero_ext wz (Z_of_nat n * 8) x)). 
  decEq. symmetry. apply Int.zero_ext_mod; try solve [omega]. 
Qed.

Lemma int_of_bytes_of_int_2:
  forall n x,
  (n = 1 \/ n = 2)%nat ->
  Int.repr 31 (int_of_bytes (bytes_of_int n (Int.unsigned 31 x))) = 
    Int.zero_ext 31 (Z_of_nat n * 8) x.
Proof.
  intros. apply int_of_bytes_of_int_wz.
  destruct H; subst n; compute; auto.
Qed.

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply (Int.eqm_samerepr 7). red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma bytes_of_int_mod':
  forall z x y,
  z >= 0 ->
  Int.eqmod (two_p (z * 8)) x y ->
  bytes_of_int (nat_of_Z z) x =
  bytes_of_int (nat_of_Z z) y.
Proof.
  intros.
  rewrite <- (@nat_of_Z_eq z) in H0; auto.
  apply bytes_of_int_mod; auto.
Qed.

Lemma bytes_of_int_prop1: forall n z,
  (n > 0)%nat ->
  exists b, exists bl, 
    bytes_of_int n z = b::bl.
Proof. 
  destruct n; intros.
    contradict H; omega.

    simpl.
    exists (Int.repr 7 z).
    exists (bytes_of_int n (z/256)).
    auto.
Qed.

Parameter big_endian: bool.

Definition rev_if_be (A:Type) (l: list A) : list A :=
  if big_endian then List.rev l else l.

Lemma rev_if_be_involutive:
  forall A l, rev_if_be A (rev_if_be A l) = l.
Proof.
  intros; unfold rev_if_be; destruct big_endian. 
  apply List.rev_involutive. 
  auto.
Qed.

Lemma rev_if_be_length:
  forall A l, length (rev_if_be A l) = length l.
Proof.
  intros; unfold rev_if_be; destruct big_endian.
  apply List.rev_length.
  auto.
Qed.

Definition encode_int (c:memory_chunk) (wz:nat) (x: Int.int wz) : list byte :=
  let n := Int.unsigned wz x in
  rev_if_be _ (match c with
  | Mint wz0 => bytes_of_int (nat_of_Z (bytesize_chunk wz0)) n
  | Mfloat32 => bytes_of_int 4%nat 0
  | Mfloat64 => bytes_of_int 8%nat 0
  end).

Definition decode_int (wz:nat) (b: list byte) : Int.int wz :=
  let b' := rev_if_be _ b in Int.repr wz (int_of_bytes b').

Definition decode_float32 (b: list byte) : Int.int 31 := Int.zero 31.

Definition decode_float64 (b: list byte) : Int.int 63 := Int.zero 63.

Lemma encode_int_length:
  forall chunk wz x, length (encode_int chunk wz x) = size_chunk_nat chunk.
Proof.
  intros. unfold encode_int. rewrite rev_if_be_length.
  destruct chunk; rewrite length_bytes_of_int; reflexivity.
Qed.

Lemma decode_encode_int:
  forall c wz x,
  match c with
  | Mint wz0 => 
      decode_int wz0 (encode_int c wz x) = Int.repr wz0 (Int.unsigned wz x)
  | Mfloat32 => decode_float32 (encode_int c wz x) = Int.zero 31
  | Mfloat64 => decode_float64 (encode_int c wz x) = Int.zero 63
  end.
Proof.
  intros. 
  unfold decode_int, encode_int, decode_float32, decode_float64; destruct c; 
  auto; rewrite rev_if_be_involutive.

  rewrite int_of_bytes_of_int.
  assert (J:=@bytesize_chunk_pos n).
  rewrite nat_of_Z_eq; try omega.
  apply Int.eqm_samerepr. 
  unfold Int.eqm, Int.eqmod.
  unfold Int.modulus.
  unfold Int.wordsize.
  unfold bytesize_chunk.  
  assert (8 > 0) as J'. omega.
  assert (J1:=@ZRdiv_prop1 (Z_of_nat (S n)) 8 J').
  assert (8 * ZRdiv (Z_of_nat (S n)) 8 = ZRdiv (Z_of_nat (S n)) 8 * 8) as EQ.
    auto with zarith.
  rewrite EQ in J1. clear EQ.
  assert (J2:=Z_of_S_gt_O n).
  assert (two_power_nat (S n) = two_p (Z_of_nat (S n))) as EQ.
    simpl.
    rewrite two_power_pos_nat.
    rewrite S_eq_nat_of_P_o_P_of_succ_nat. auto.

  rewrite EQ. clear EQ.
  (* 
     let m1 = ZRdiv (Z_of_nat (S n)) 8 * 8
     let m2 = S n
     x % (2^m1) = 2^m1 * k0 + x for some k0
     so,
     x % (2^m1) = 2^m2 * (2^(m1-m2) * k0) + x
     so (2^(m1-m2) * k0) is the witness
  *) 
  remember (ZRdiv (Z_of_nat (S n)) 8 * 8) as m1.
  remember (Z_of_nat (S n)) as m2.    
  rewrite Zmod_eq with (a:=Int.unsigned wz x) (b:=two_p m1).
    remember (Int.unsigned wz x / two_p m1) as k0.
    exists ( - two_p (m1 - m2) * k0).
    ring_simplify.
    rewrite <- Zmult_assoc.
    rewrite <- two_p_is_exp; auto with zarith.
    assert (m1 = m1 - m2 + m2) as EQ. auto with zarith.
    rewrite <- EQ. clear EQ.
    auto.

    apply two_p_gt_ZERO. auto with zarith.
Qed.

(** * Encoding and decoding floats *)

Definition encode_float (c: memory_chunk) (f: float) : list byte :=
  rev_if_be _ (match c with
  | Mint wz => bytes_of_int (bytesize_chunk_nat wz) 0
  | Mfloat32 => bytes_of_int 4%nat (Int.unsigned 31 (Float.bits_of_single f))
  | Mfloat64 => bytes_of_int 8%nat (Int.unsigned 63 (Float.bits_of_double f))
  end).

Definition decode_float (c: memory_chunk) (b: list byte) : float :=
  let b' := rev_if_be _ b in
  match c with
  | Mfloat32 => Float.single_of_bits (Int.repr 31 (int_of_bytes b'))
  | Mfloat64 => Float.double_of_bits (Int.repr 63 (int_of_bytes b'))
  | _ => Float.zero
  end.

Lemma encode_float_length:
  forall chunk n, length(encode_float chunk n) = size_chunk_nat chunk.
Proof.
  unfold encode_float; intros. 
  rewrite rev_if_be_length. 
  destruct chunk; try solve [
    apply length_bytes_of_int |
    unfold size_chunk_nat, size_chunk;
      rewrite Z_of_nat_eq; apply length_bytes_of_int].
Qed.

Lemma decode_encode_float32: forall n,
  decode_float Mfloat32 (encode_float Mfloat32 n) = Float.singleoffloat n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int. rewrite <- Float.single_of_bits_of_single. 
  decEq. 
  transitivity (Int.repr 31 (Int.unsigned 31 (Float.bits_of_single n))). 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  apply Int.repr_unsigned.
Qed.

Lemma decode_encode_float64: forall n,
  decode_float Mfloat64 (encode_float Mfloat64 n) = n.
Proof.
  intros; unfold decode_float, encode_float. 
  rewrite rev_if_be_involutive. 
  rewrite int_of_bytes_of_int.
  set (x := Float.bits_of_double n).
  transitivity (Float.double_of_bits(Int.repr 63 (Int.unsigned 63 x))).
  decEq. 
  apply Int.eqm_samerepr. apply Int.eqm_sym. apply Int.eqmod_mod. apply two_p_gt_ZERO. omega. 
  rewrite Int.repr_unsigned. apply Float.double_of_bits_of_double.
Qed.

Lemma encode_float32_cast:
  forall f,
  encode_float Mfloat32 (Float.singleoffloat f) = encode_float Mfloat32 f.
Proof.
  intros; unfold encode_float. decEq. decEq. decEq. 
  apply Float.bits_of_singleoffloat.
Qed.

Lemma decode_float32_cast:
  forall l,
  Float.singleoffloat (decode_float Mfloat32 l) = decode_float Mfloat32 l.
Proof.
  intros; unfold decode_float. rewrite Float.singleoffloat_of_bits. auto.
Qed.

(** * Encoding and decoding values *)

Definition inj_bytes (wz:nat) (bl: list byte) : list memval :=
  List.map (Byte wz) bl.

Fixpoint proj_bytes (wz:nat) (vl: list memval) : option (list byte) :=
  match vl with
  | nil => Some nil
  | Byte wz0 b :: vl' =>
      if eq_nat_dec wz0 wz then
        match proj_bytes wz vl' with None => None | Some bl => Some(b :: bl) end
      else None
  | _ => None
  end.

Remark length_inj_bytes:
  forall wz bl, length (inj_bytes wz bl) = length bl.
Proof.
  intros. apply List.map_length.
Qed.

Remark proj_inj_bytes:
  forall wz bl, proj_bytes wz (inj_bytes wz bl) = Some bl.
Proof.
  induction bl; simpl; auto. 
    rewrite IHbl.
    destruct (eq_nat_dec wz wz); auto.
      contradict n; auto.
Qed.

Lemma inj_proj_bytes:
  forall wz cl bl, proj_bytes wz cl = Some bl -> cl = inj_bytes wz bl.
Proof.
  induction cl; simpl; intros.
  inv H; auto.
  destruct a; try congruence.
  destruct (eq_nat_dec n wz); try solve [inv H].
  destruct (proj_bytes wz cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_pointer (n: nat) (b: block) (ofs: Int.int 31) {struct n} 
  : list memval :=
  match n with
  | O => nil
  | S m => Pointer b ofs m :: inj_pointer m b ofs
  end.

Fixpoint check_pointer (n: nat) (b: block) (ofs: Int.int 31) (vl: list memval) 
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Pointer b' ofs' m' :: vl' =>
      eq_block b b' && Int.eq_dec 31 ofs ofs' && beq_nat m m' && 
      check_pointer m b ofs vl'
  | _, _ => false
  end.

Definition proj_pointer (vl: list memval) : val :=
  match vl with
  | Pointer b ofs n :: vl' =>
      if check_pointer (size_chunk_nat Mint32) b ofs vl
      then Vptr b ofs
      else Vundef
  | _ => Vundef
  end.

Lemma inj_pointer_length:
  forall b ofs n, List.length(inj_pointer n b ofs) = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma check_inj_pointer:
  forall b ofs n, check_pointer n b ofs (inj_pointer n b ofs) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.  
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Fixpoint inj_ipointer (n: nat) (i: Int.int 31) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => IPointer i m :: inj_ipointer m i
  end.

Fixpoint check_ipointer (n: nat) (i: Int.int 31) (vl: list memval) {struct n} 
  : bool :=
  match n, vl with
  | O, nil => true
  | S m, IPointer i' m':: vl' =>
      Int.eq_dec 31 i i' && beq_nat m m' && check_ipointer m i vl'
  | _, _ => false
  end.

Definition proj_ipointer (vl: list memval) : val :=
  match vl with
  | IPointer i n :: vl' =>
      if check_ipointer (size_chunk_nat Mint32) i vl
      then Vinttoptr i
      else Vundef
  | _ => Vundef
  end.

Lemma inj_ipointer_length:
  forall i n, List.length(inj_ipointer n i) = n.
Proof.
  induction n; simpl; congruence.
Qed.

Lemma check_inj_ipointer:
  forall i n, check_ipointer n i (inj_ipointer n i) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true.  
  rewrite <- beq_nat_refl. simpl; auto.
Qed.

Definition wz_of_chunk (chunk: memory_chunk) : nat :=
  match chunk with
  | Mint wz => wz
  | Mfloat32 => 31%nat
  | Mfloat64 => 63%nat
  end.
  
Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  match v, chunk with
  | Vptr b ofs, Mint wz => 
      if (eq_nat_dec wz 31) then inj_pointer (size_chunk_nat (Mint32)) b ofs
      else list_repeat (size_chunk_nat chunk) Undef
  | Vinttoptr i, Mint wz => 
      if (eq_nat_dec wz 31) then inj_ipointer (size_chunk_nat (Mint wz)) i
      else list_repeat (size_chunk_nat chunk) Undef
  | Vint wz n, _ => inj_bytes (wz_of_chunk chunk) (encode_int chunk wz n)
  | Vfloat f, _ => inj_bytes (wz_of_chunk chunk) (encode_float chunk f)
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match proj_bytes (wz_of_chunk chunk) vl with
  | Some bl =>
      match chunk with
      | Mint _ => Vint (wz_of_chunk chunk) (decode_int (wz_of_chunk chunk) bl)
      | Mfloat32 | Mfloat64 => Vfloat(decode_float chunk bl)
      end
  | None =>
      match chunk with
      | Mint wz => 
          if eq_nat_dec wz 31 then
            match proj_pointer vl with
            | Vundef => proj_ipointer vl
            | v => v
            end
          else Vundef 
      | _ => Vundef
      end
  end.

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. destruct v; simpl.
  apply length_list_repeat.
  rewrite length_inj_bytes. apply encode_int_length.
  rewrite length_inj_bytes. apply encode_float_length.

  destruct chunk; try (apply length_list_repeat). 
    destruct (eq_nat_dec n 31); subst; auto.
      apply length_list_repeat.

  destruct chunk; try (apply length_list_repeat). 
    destruct (eq_nat_dec n 31); subst; auto.
      apply length_list_repeat.
Qed.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) 
  : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef
  | Vint wz n, Mint wz1, Mint wz2 => 
      if eq_nat_dec wz1 wz2 then 
        v2 = Vint wz2 (Int.repr wz2 (Int.unsigned wz n)) 
      else True
  | Vint wz n, Mint wz', Mfloat32 => 
      if eq_nat_dec wz' 31
      then v2 = Vfloat(decode_float Mfloat32 (encode_int (Mint32) wz n))
      else True
  | Vint wz n, _, _ => True   (* nothing interesting to say about v2 *)
  | Vptr b ofs, Mint wz1, Mint wz2 => 
      if eq_nat_dec wz1 31 && eq_nat_dec wz2 31 
      then v2 = Vptr b ofs else v2 = Vundef
  | Vptr b ofs, _, _ => v2 = Vundef
  | Vinttoptr i, Mint wz1, Mint wz2 => 
      if eq_nat_dec wz1 31 && eq_nat_dec wz2 31
      then v2 = Vinttoptr i else v2 = Vundef
  | Vinttoptr i, _, _ => v2 = Vundef
  | Vfloat f, Mfloat32, Mfloat32 => v2 = Vfloat(Float.singleoffloat f)
  | Vfloat f, Mfloat32, Mint wz => 
      if eq_nat_dec wz 31
      then v2 = Vint 31 (decode_int 31 (encode_float Mfloat32 f))
      else True
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  end.

Lemma proj_bytes_inj_pointer:
  forall wz n b i, (n > 0)%nat -> proj_bytes wz (inj_pointer n b i) = None.
Proof.
  induction n; simpl; auto. 
    intros. contradict H; omega.
Qed.

Lemma inj_pointer_inv : forall n b i,
  (n > 0)%nat -> 
  exists m, exists tl, inj_pointer n b i = Pointer b i m :: tl /\ n = S m.
Proof.
  destruct n; intros.
    contradict H; omega.
    simpl. exists n. exists (inj_pointer n b i). auto.
Qed.

Lemma bytesize_chunk_nat__size_chunk_nat : forall n,
  size_chunk_nat (Mint n) = bytesize_chunk_nat n.
Proof.
  intros. 
  unfold size_chunk_nat, bytesize_chunk_nat, size_chunk, bytesize_chunk.
  auto.
Qed.

Lemma list_repeat_cons_inv : forall A m (a:A) b v,
  a :: b = list_repeat m v ->
  a = v /\
  exists m', S m' = m /\ b = list_repeat m' v.
Proof.
  induction m; intros; simpl in *.
    inversion H.

    inversion H; subst.
    split; auto.
    exists m. split; auto.
Qed.

Lemma nonempty_list_repeat : forall A m (v:A),
  (m > 0)%nat -> nil <> list_repeat m v.
Proof.
  induction m; simpl; intros.
    contradict H; omega.
    intro J. inversion J.
Qed.

Lemma proj_bytes_undef' : forall n m,
  (m > 0)%nat ->
  proj_bytes n (list_repeat m Undef) = None.
Proof.
  intros.
  remember (list_repeat m Undef) as L.
  generalize dependent m.
  generalize dependent n.
  induction L; intros; simpl.
    contradict HeqL.
    apply nonempty_list_repeat; auto.

    apply list_repeat_cons_inv in HeqL.
    destruct HeqL as [H1 [m' [H2 H3]]]; subst; auto.
Qed.

Remark proj_pointer_undef':
  forall n, proj_pointer (list_repeat n Undef) = Vundef.
Proof.
  induction n; simpl; auto.
Qed.

Remark proj_ipointer_undef':
  forall n, proj_ipointer (list_repeat n Undef) = Vundef.
Proof.
  induction n; simpl; auto.
Qed.

Lemma proj_pointer_inj_pointer:
  forall b i, proj_pointer (inj_pointer (size_chunk_nat Mint32) b i) = Vptr b i.
Proof.
  intros.
  Opaque check_pointer. 
  simpl.
  rewrite check_inj_pointer. auto.
  Transparent check_pointer. 
Qed.

Lemma proj_bytes_inj_ipointer:
  forall wz n i, (n > 0)%nat -> proj_bytes wz (inj_ipointer n i) = None.
Proof.
  induction n; simpl; intros; auto. 
    contradict H; omega.
Qed.

Lemma proj_pointer_inj_ipointer:
  forall i, proj_pointer (inj_ipointer (size_chunk_nat Mint32) i) = Vundef.
Proof.
  intros. simpl. auto.
Qed.

Lemma proj_ipointer_inj_ipointer:
  forall i, proj_ipointer (inj_ipointer (size_chunk_nat Mint32) i) = Vinttoptr i.
Proof.
  intros.
  Opaque check_ipointer. 
  simpl.
  rewrite check_inj_ipointer. auto.
  Transparent check_ipointer. 
Qed.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intros. destruct v.
(* Vundef *)
  simpl. destruct (size_chunk_nat_pos chunk1) as [psz EQ].
  rewrite EQ. simpl.
  unfold decode_val. simpl. 
  destruct chunk2; auto.
  destruct (eq_nat_dec n 31); auto.
(* Vint *)
  simpl.
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val; simpl.
    destruct (eq_nat_dec n n0); subst; simpl; auto.
      rewrite proj_inj_bytes.
      rewrite decode_encode_int with (c:=Mint n0). auto.

    destruct (eq_nat_dec n 31); subst; auto.
    rewrite proj_inj_bytes. auto.
(* Vfloat *)
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto; unfold decode_val.
    destruct (eq_nat_dec n 31); subst; auto.
    rewrite proj_inj_bytes. auto.

    rewrite proj_inj_bytes. 
    rewrite decode_encode_float32. auto.

    rewrite proj_inj_bytes. 
    rewrite decode_encode_float64. auto.
(* Vptr *)
  assert (J:=@size_chunk_nat_pos' chunk1).
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto.
    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_inj_pointer; auto using size_chunk_nat_pos'.
      rewrite proj_pointer_inj_pointer.
      destruct (eq_nat_dec n0 31); subst; simpl; auto.
 
      simpl. rewrite proj_bytes_undef'; auto. rewrite proj_pointer_undef'.
      rewrite proj_ipointer_undef'.
      destruct (eq_nat_dec n0 31); subst; simpl; auto.
    destruct (eq_nat_dec n 31); subst; auto.
       rewrite proj_bytes_undef'; auto. 
    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_undef'; auto. 
    rewrite proj_bytes_undef'; auto.
    destruct (eq_nat_dec n 31); subst; auto.
    rewrite proj_bytes_undef'; auto.
    destruct (eq_nat_dec n 31); subst; auto.
(* Vint2ptr *)
  assert (J:=@size_chunk_nat_pos' chunk1).
  unfold decode_val, encode_val, decode_encode_val;
  destruct chunk1; auto; destruct chunk2; auto.
    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_inj_ipointer; auto using size_chunk_nat_pos'.
      rewrite proj_pointer_inj_ipointer.
      rewrite proj_ipointer_inj_ipointer.
      destruct (eq_nat_dec n0 31); subst; simpl; auto.
 
      simpl. rewrite proj_bytes_undef'; auto. rewrite proj_pointer_undef'.
      rewrite proj_ipointer_undef'.
      destruct (eq_nat_dec n0 31); subst; simpl; auto.
    destruct (eq_nat_dec n 31); subst; auto.
       rewrite proj_bytes_undef'; auto. 
    destruct (eq_nat_dec n 31); subst; auto.
      rewrite proj_bytes_undef'; auto. 
    rewrite proj_bytes_undef'; auto.
    destruct (eq_nat_dec n 31); subst; auto.
    rewrite proj_bytes_undef'; auto.
    destruct (eq_nat_dec n 31); subst; auto.
Qed.

Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  chunk_eq chunk1 chunk2 ->
  Val.has_type v1 (type_of_chunk chunk1) ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
  intros.
  destruct v1.
  simpl in *. destruct chunk2; simpl; auto.

  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  unfold chunk_eq in H0. destruct H0; subst.
  destruct (eq_nat_dec n0 n0); auto.
    contradict n; auto.

  unfold chunk_eq in H0. destruct H0.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.

  unfold chunk_eq in H0. destruct H0.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  subst. destruct (eq_nat_dec n0 31); auto.

  unfold chunk_eq in H0. destruct H0.
  red in H1.
  destruct chunk1; simpl in H1; try contradiction;
  destruct chunk2; simpl in *; discriminate || auto.
  subst. destruct (eq_nat_dec n0 31); auto.
Qed.

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val.
  destruct chunk; simpl; auto. 

    unfold decode_int.    
    destruct (proj_bytes n cl); simpl; auto.
      destruct (eq_nat_dec n 31); simpl; auto.
        unfold proj_pointer. unfold proj_ipointer.
        destruct cl; try solve [simpl; auto].
          destruct m; try solve [simpl; auto].
            destruct (check_pointer (size_chunk_nat Mint32) b i 
                       (Pointer b i n0::cl)); simpl; auto.            
            destruct (check_ipointer (size_chunk_nat Mint32) i 
                       (IPointer i n0::cl)); simpl; auto.

    destruct (proj_bytes 31 cl); simpl; auto.
    destruct (proj_bytes 63 cl); simpl; auto.
Qed.

(*
Lemma encode_val_int8_signed_unsigned:
  forall v, encode_val Mint8signed v = encode_val Mint8unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int16_signed_unsigned:
  forall v, encode_val Mint16signed v = encode_val Mint16unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.

Lemma encode_val_int8_zero_ext:
  forall n, encode_val Mint8unsigned (Vint (Int.zero_ext 8 n)) = encode_val Mint8unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int8_zero_ext. auto.
Qed.

Lemma encode_val_int8_sign_ext:
  forall n, encode_val Mint8signed (Vint (Int.sign_ext 8 n)) = encode_val Mint8signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int8_sign_ext. auto.
Qed.

Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16unsigned (Vint (Int.zero_ext 16 n)) = encode_val Mint16unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_zero_ext. auto.
Qed.

Lemma encode_val_int16_sign_ext:
  forall n, encode_val Mint16signed (Vint (Int.sign_ext 16 n)) = encode_val Mint16signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite encode_int16_sign_ext. auto.
Qed.
*)

Lemma decode_val_int_inv:
  forall chunk cl n,
  decode_val chunk cl = Vint (wz_of_chunk chunk) n ->
  type_of_chunk chunk = Tint /\
  exists bytes, proj_bytes (wz_of_chunk chunk) cl = Some bytes /\ 
    n = decode_int (wz_of_chunk chunk) bytes.
Proof.
  intros until n. unfold decode_val. 
  destruct (proj_bytes (wz_of_chunk chunk) cl).
Opaque decode_int.
    destruct chunk; intro EQ; inv EQ; split; auto; exists l; auto.

    destruct chunk; try congruence. 
    destruct (eq_nat_dec n0 31); subst; try congruence. 
    unfold proj_pointer, proj_ipointer.
    destruct cl; try congruence. 
    destruct m; try congruence.
      destruct (check_pointer (size_chunk_nat Mint32) b i 
        (Pointer b i n0 :: cl)); congruence.
      destruct (check_ipointer (size_chunk_nat Mint32) i 
        (IPointer i n0 :: cl)); congruence.
Qed.

Lemma decode_val_float_inv:
  forall chunk cl f,
  decode_val chunk cl = Vfloat f ->
  type_of_chunk chunk = Tfloat /\
  exists bytes, proj_bytes (wz_of_chunk chunk) cl = Some bytes /\ 
    f = decode_float chunk bytes.
Proof.
  intros until f. unfold decode_val. 
  destruct (proj_bytes (wz_of_chunk chunk) cl).
    destruct chunk; intro EQ; inv EQ; split; auto; exists l; auto.

    destruct chunk; try congruence.
    destruct (eq_nat_dec n 31); subst; try congruence.
    unfold proj_pointer. unfold proj_ipointer.
    destruct cl; try congruence. 
    destruct m; try congruence.
      destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: cl));
        congruence.
      destruct (check_ipointer (size_chunk_nat Mint32) i (IPointer i n :: cl));
        congruence.
Qed.

Lemma decode_val_cast:
  forall chunk l,
  let v := decode_val chunk l in
  match chunk with
  | Mint wz => True
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto.
  destruct (proj_bytes (wz_of_chunk Mfloat32) l); auto.
  unfold Val.singleoffloat. decEq. symmetry. apply decode_float32_cast.
Qed.

(** Pointers cannot be forged. *)

Definition memval_valid_first (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n = pred (size_chunk_nat Mint32)
  | IPointer i n => n = pred (size_chunk_nat Mint32)
  | _ => True
  end.

Definition memval_valid_cont (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n <> pred (size_chunk_nat Mint32)  
  | IPointer i n => n <> pred (size_chunk_nat Mint32)  
  | _ => True
  end.

Inductive encoding_shape: list memval -> Prop :=
  | encoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 ->
      (forall mv, In mv mvl -> memval_valid_cont mv) ->
      encoding_shape (mv1 :: mvl).

Lemma encode_val_shape:
  forall chunk v, encoding_shape (encode_val chunk v).
Proof.
  intros.
  destruct (size_chunk_nat_pos chunk) as [sz1 EQ].
  assert (encoding_shape (list_repeat (size_chunk_nat chunk) Undef)).
    rewrite EQ; simpl; constructor. exact I.
    intros. replace mv with Undef. exact I. symmetry; eapply in_list_repeat; eauto.
  assert (forall bl, length bl = size_chunk_nat chunk ->
          encoding_shape (inj_bytes (wz_of_chunk chunk) bl)).
    intros. destruct bl; simpl in *. congruence.
    constructor. exact I. unfold inj_bytes. intros.
    exploit list_in_map_inv; eauto. intros [x [A B]]. subst mv. exact I.
  destruct v; simpl.
    auto.
    apply H0. apply encode_int_length.
    apply H0. apply encode_float_length.

    destruct chunk; auto.
    destruct (eq_nat_dec n 31); auto.
      constructor. 
        red. auto.
        simpl; intros. intuition; subst mv; red; simpl; congruence.

    destruct chunk; auto.
    destruct (eq_nat_dec n 31); subst; simpl; auto. 
      constructor. 
        red. auto.
        simpl; intros. intuition; subst mv; red; simpl; congruence.
Qed.

Lemma check_pointer_inv:
  forall b ofs n mv,
  check_pointer n b ofs mv = true -> mv = inj_pointer n b ofs.
Proof.
  induction n; destruct mv; simpl. 
  auto.
  congruence.
  congruence.
  destruct m; try congruence. intro. 
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
  destruct (andb_prop _ _ H2).
  decEq. decEq. symmetry; eapply proj_sumbool_true; eauto.
  symmetry; eapply proj_sumbool_true; eauto.
  symmetry; apply beq_nat_true; auto.
  auto.
Qed.

Lemma check_ipointer_inv:
  forall i n mv,
  check_ipointer n i mv = true -> mv = inj_ipointer n i.
Proof.
  induction n; destruct mv; simpl. 
  auto.
  congruence.
  congruence.
  destruct m; try congruence. intro. 
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
  decEq. decEq. symmetry; eapply proj_sumbool_true; eauto.
  symmetry; apply beq_nat_true; auto.
  auto.
Qed.

Inductive decoding_shape: list memval -> Prop :=
  | decoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 -> mv1 <> Undef ->
      (forall mv, In mv mvl -> memval_valid_cont mv /\ mv <> Undef) ->
      decoding_shape (mv1 :: mvl).

Lemma decode_val_shape:
  forall chunk mvl,
  List.length mvl = size_chunk_nat chunk ->
  decode_val chunk mvl = Vundef \/ decoding_shape mvl.
Proof.
  intros. destruct (size_chunk_nat_pos chunk) as [sz EQ].
  unfold decode_val.
  caseEq (proj_bytes (wz_of_chunk chunk) mvl).
    intros bl PROJ. right. exploit inj_proj_bytes; eauto. intros. subst mvl.
    destruct bl; simpl in H. congruence. simpl.
    constructor.
      red; auto. 
      congruence.
      unfold inj_bytes; intros. exploit list_in_map_inv; eauto. intros [b [A B]].
      subst mv. 
      split. 
        red; auto. 
        congruence.

    intros. destruct chunk; auto. destruct (eq_nat_dec n 31); subst; auto.
    unfold proj_pointer, proj_ipointer.
    destruct mvl; auto. 
    destruct m; auto.
      caseEq (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: mvl));
        auto.
      intros. right. exploit check_pointer_inv; eauto. simpl; intros; inv H2.
      constructor. 
        red. auto.  
        congruence.
        simpl; intros. intuition; subst mv; simpl; congruence.

      caseEq (check_ipointer (size_chunk_nat Mint32) i (IPointer i n :: mvl));
        auto.
      intros. right. exploit check_ipointer_inv; eauto. simpl; intros; inv H2.
      constructor. 
        red. auto.  
        congruence.
        simpl; intros. intuition; subst mv; simpl; congruence.
Qed.

Lemma encode_val_pointer_inv:
  forall chunk v b ofs n mvl,
  encode_val chunk v = Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs /\ 
    mvl = inj_pointer (pred (size_chunk_nat Mint32)) b ofs.
Proof.
  intros until mvl.
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  unfold encode_val. rewrite SZ. 
  destruct v.
    simpl. congruence.

    generalize (encode_int_length chunk wz i). 
    destruct (encode_int chunk wz i); simpl; congruence.

    generalize (encode_float_length chunk f). 
    destruct (encode_float chunk f); simpl; congruence.

    destruct chunk; try (simpl; congruence).
    destruct (eq_nat_dec n0 31); subst; try (simpl; congruence).
    simpl. intuition congruence.

    destruct chunk; try (simpl; congruence).
    destruct (eq_nat_dec n0 31); subst; try (simpl; congruence).
Qed.

Lemma encode_val_ipointer_inv:
  forall chunk v i n mvl,
  encode_val chunk v = IPointer i n :: mvl ->
  chunk = Mint32 /\ v = Vinttoptr i /\ 
    mvl = inj_ipointer (pred (size_chunk_nat Mint32)) i.
Proof.
  intros until mvl.
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  unfold encode_val. rewrite SZ. 
  destruct v.
    simpl. congruence.

    generalize (encode_int_length chunk wz i0). 
    destruct (encode_int chunk wz i0); simpl; congruence.

    generalize (encode_float_length chunk f). 
    destruct (encode_float chunk f); simpl; congruence.

    destruct chunk; try (simpl; congruence).
    destruct (eq_nat_dec n0 31); subst; try (simpl; congruence).

    destruct chunk; try (simpl; congruence).
    destruct (eq_nat_dec n0 31); subst; try (simpl; congruence).
    simpl. intuition congruence.
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = inj_pointer (size_chunk_nat Mint32) b ofs.
Proof.
  intros until ofs; unfold decode_val.
  destruct (proj_bytes (wz_of_chunk chunk) mvl).
    destruct chunk; congruence.

    destruct chunk; try congruence.
    destruct (eq_nat_dec n 31); subst; try congruence.
    unfold proj_pointer. 
    Opaque check_ipointer.
    destruct mvl; try solve [intro J; inversion J].
    destruct m; try solve [intro J; inversion J].
      case_eq (check_pointer (size_chunk_nat Mint32) b0 i 
        (Pointer b0 i n :: mvl)); intros.
        inv H0. split; auto. apply check_pointer_inv; auto.
        inv H0.
      intro J. simpl in J.
      destruct (check_ipointer (size_chunk_nat Mint32) i (IPointer i n :: mvl));
        inversion J.
    Transparent check_ipointer.
Qed.

Lemma decode_val_ipointer_inv:
  forall chunk mvl i,
  decode_val chunk mvl = Vinttoptr i ->
  chunk = Mint32 /\ mvl = inj_ipointer (size_chunk_nat Mint32) i.
Proof.
  intros until i; unfold decode_val.
  destruct (proj_bytes (wz_of_chunk chunk) mvl).
    destruct chunk; congruence.

    destruct chunk; try congruence.
    destruct (eq_nat_dec n 31); subst; try congruence.
    unfold proj_ipointer. 
    unfold proj_pointer.
    Opaque check_pointer.
    destruct mvl; try congruence.
    destruct m; try congruence.
      case_eq (check_pointer (size_chunk_nat Mint32) b i0 
        (Pointer b i0 n :: mvl)); intros.
        inv H0. inv H0.

      case_eq (check_ipointer (size_chunk_nat Mint32) i0 (IPointer i0 n :: mvl));
        intros.
        inv H0. split; auto. apply check_ipointer_inv; auto.
        inv H0.
    Transparent check_pointer.
Qed.

Inductive pointer_encoding_shape: list memval -> Prop :=
  | pointer_encoding_shape_intro: forall mv1 mvl,
      ~memval_valid_cont mv1 ->
      (forall mv, In mv mvl -> ~memval_valid_first mv) ->
      pointer_encoding_shape (mv1 :: mvl).

Lemma encode_pointer_shape:
  forall b ofs, pointer_encoding_shape (encode_val Mint32 (Vptr b ofs)).
Proof.
  intros. simpl. 
  constructor.
    unfold memval_valid_cont. red; intro. elim H. auto.
    unfold memval_valid_first. simpl; intros; intuition; subst mv; congruence.
Qed.

Lemma encode_ipointer_shape:
  forall i, pointer_encoding_shape (encode_val Mint32 (Vinttoptr i)).
Proof.
  intros. simpl. 
  constructor.
    unfold memval_valid_cont. red; intro. elim H. auto.
    unfold memval_valid_first. simpl; intros; intuition; subst mv; congruence.
Qed.

Lemma decode_pointer_shape:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ pointer_encoding_shape mvl.
Proof.
  intros. exploit decode_val_pointer_inv; eauto. intros [A B].
  split; auto. subst mvl. 
  assert (J:=@encode_pointer_shape b ofs).
  unfold encode_val in J.
  simpl in J. auto.
Qed.

Lemma decode_ipointer_shape:
  forall chunk mvl i,
  decode_val chunk mvl = Vinttoptr i ->
  chunk = Mint32 /\ pointer_encoding_shape mvl.
Proof.
  intros. exploit decode_val_ipointer_inv; eauto. intros [A B].
  split; auto. subst mvl.
  assert (J:=@encode_ipointer_shape i).
  unfold encode_val in J.
  simpl in J. auto.
Qed.

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall wz n, memval_inject f (Byte wz n) (Byte wz n)
  | memval_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta n,
      f b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      memval_inject f (Pointer b1 ofs1 n) (Pointer b2 ofs2 n)
  | memval_inject_inttoptr:
      forall i n, memval_inject f (IPointer i n) (IPointer i n)
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr: forall f f' v1 v2, 
  memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. rewrite (H0 _ _ _ H1). reflexivity. auto.
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [val_inject]. *)

Lemma proj_bytes_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n bl,
  proj_bytes n vl = Some bl ->
  proj_bytes n vl' = Some bl.
Proof.
  induction 1; simpl. congruence.
  inv H; try congruence.

  intros.
  destruct (eq_nat_dec wz n0); auto.
  remember (proj_bytes n0 al) as R.
  destruct R.
    inv H. rewrite (IHlist_forall2 n0 l); auto.
    congruence.      
Qed.

Lemma check_pointer_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = true ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add 31 ofs (Int.repr 31 delta)) vl' = true.
Proof.
  induction 1; intros; destruct n; simpl in *; auto.
  inv H; auto.
  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H).
  destruct (andb_prop _ _ H5).
  assert (n = n0) by (apply beq_nat_true; auto).
  assert (b = b0) by (eapply proj_sumbool_true; eauto).
  assert (ofs = ofs1) by (eapply proj_sumbool_true; eauto).
  subst. rewrite H3 in H2; inv H2.
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.
  rewrite <- beq_nat_refl. simpl. eauto.
  congruence.
Qed.

Lemma check_ipointer_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n i,
  check_ipointer n i vl = true ->
  check_ipointer n i vl' = true. 
Proof.
  induction 1; intros; destruct n; simpl in *; auto. 
  inv H; auto.

  destruct (andb_prop _ _ H1). destruct (andb_prop _ _ H).
  apply IHlist_forall2 in H2.
  congruence.

  inv H1.
Qed.

Lemma proj_pointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_pointer vl1) (proj_pointer vl2).
Proof.
  intros. unfold proj_pointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_pointer (size_chunk_nat Mint32) b0 ofs1 
             (Pointer b0 ofs1 n :: al)); intros.
  exploit check_pointer_inject. eexact H. eauto. eauto. 
  intro. rewrite H4. econstructor; eauto. 
  constructor.
Qed.

Lemma proj_ipointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (proj_ipointer vl1) (proj_ipointer vl2).
Proof.
  intros. unfold proj_ipointer.
  inversion H; subst. auto. inversion H0; subst; auto.
  case_eq (check_ipointer (size_chunk_nat Mint32) i 
             (IPointer i n :: al)); intros.
  exploit check_ipointer_inject. eexact H. eauto. eauto. 
  intro. rewrite H3. econstructor; eauto. 
  constructor.
Qed.

Lemma proj_bytes_not_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  proj_bytes n vl = None -> proj_bytes n vl' <> None -> In Undef vl.
Proof.
  induction 1; simpl; intros.
    congruence.
    inv H; try congruence; auto.
    destruct (eq_nat_dec wz n); subst; auto.
      remember (proj_bytes n al) as R.
      remember (proj_bytes n bl) as R'.
      destruct R; destruct R';
        try solve [inversion H1 | inversion H2 | contradict H2; auto].
        right. eapply IHlist_forall2; eauto.
          rewrite <- HeqR'. intro. inversion H.          
      contradict H2; auto.
Qed.

Lemma check_pointer_undef:
  forall n b ofs vl,
  In Undef vl -> check_pointer n b ofs vl = false.
Proof.
  induction n; intros; simpl. 
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r. 
Qed.

Lemma check_ipointer_undef:
  forall n i vl,
  In Undef vl -> check_ipointer n i vl = false.
Proof.
  induction n; intros; simpl. 
  destruct vl. elim H. auto.
  destruct vl. auto.
  destruct m; auto. simpl in H; destruct H. congruence.
  rewrite IHn; auto. apply andb_false_r. 
Qed.

Lemma proj_pointer_undef:
  forall vl, In Undef vl -> proj_pointer vl = Vundef.
Proof.
  intros; unfold proj_pointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_pointer_undef. auto. auto.
Qed.

Lemma proj_ipointer_undef:
  forall vl, In Undef vl -> proj_ipointer vl = Vundef.
Proof.
  intros; unfold proj_ipointer.
  destruct vl; auto. destruct m; auto. 
  rewrite check_ipointer_undef. auto. auto.
Qed.

Lemma proj_bytes_undef:
  forall vl wz, In Undef vl -> proj_bytes wz vl = None.
Proof.
  induction vl; intros. 
    inversion H.   

    simpl in H.
    destruct H as [H | H]; simpl; subst; auto.
    destruct a; auto.
    destruct (eq_nat_dec n wz); subst; auto.
    rewrite IHvl; auto.
Qed.

Lemma proj_pointer_inv : forall vs,
  proj_pointer vs = Vundef \/ exists b, exists ofs, proj_pointer vs = Vptr b ofs.
Proof.
  intros.
  unfold proj_pointer.
  destruct vs; auto.
  destruct m; auto.
  destruct (check_pointer (size_chunk_nat Mint32) b i (Pointer b i n :: vs));
    auto.
    right. exists b. exists i. auto.
Qed.

Lemma proj_ipointer_inv : forall vs,
  proj_ipointer vs = Vundef \/ exists i, proj_ipointer vs = Vinttoptr i.
Proof.
  intros.
  unfold proj_ipointer.
  destruct vs; auto.
  destruct m; auto.
  destruct (check_ipointer (size_chunk_nat Mint32) i (IPointer i n :: vs)); auto.
    right. exists i. auto.
Qed.

Lemma proj_pointer_neq_proj_ipointer : forall vs,
  proj_pointer vs <> Vundef ->
  proj_ipointer vs <> Vundef ->
  False.
Proof.
  unfold proj_pointer, proj_ipointer. intros.
  destruct vs; try solve [contradict H; auto].
  destruct m; try solve [contradict H; auto].
    auto.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val.
  case_eq (proj_bytes (wz_of_chunk chunk) vl1); intros.
    exploit proj_bytes_inject; eauto. intros. rewrite H1.
    destruct chunk; constructor.
 
    destruct chunk; auto.
    destruct (eq_nat_dec n 31); subst; auto.
    case_eq (proj_bytes (wz_of_chunk (Mint 31)) vl2); intros.
      assert (In Undef vl1) as J.
        eapply proj_bytes_not_inject; eauto. 
           congruence.
      rewrite proj_pointer_undef; auto.
      rewrite proj_ipointer_undef; auto.
      destruct (@proj_pointer_inv vl1) as [J1 | [b1 [ofs1 J1]]]; rewrite J1.
        destruct (@proj_ipointer_inv vl1) as [J1' | [i1' J1']]; rewrite J1'. 
          auto.
        apply proj_ipointer_inject in H.
        rewrite J1' in H.
        destruct (@proj_pointer_inv vl2) as [J2 | [b2 [ofs2 J2]]]; rewrite J2.
          auto.

          inv H.
          case_eq (proj_pointer_neq_proj_ipointer vl2); try congruence.

        destruct (@proj_pointer_inv vl2) as [J2 | [b2 [ofs2 J2]]]; rewrite J2.
          apply proj_pointer_inject in H.
          rewrite J1 in H. rewrite J2 in H. inversion H.
           
          rewrite <- J1. rewrite <- J2.
          apply proj_pointer_inject; auto.
Qed.

(** Symmetrically, [encode_val], applied to values related by [val_inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. *)

Lemma inj_bytes_inject:
  forall f wz bl, 
    list_forall2 (memval_inject f) (inj_bytes wz bl) (inj_bytes wz bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma repeat_Undef_inject_any:
  forall f vl,
  list_forall2 (memval_inject f) (list_repeat (length vl) Undef) vl.
Proof.
  induction vl; simpl; constructor; auto. constructor. 
Qed.  

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.  

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. inv H; simpl.
    apply inj_bytes_inject.
    apply inj_bytes_inject.

    destruct chunk; try apply repeat_Undef_inject_self.
    destruct (eq_nat_dec n 31); subst; try apply repeat_Undef_inject_self.
      simpl; repeat econstructor; auto.

    destruct chunk; try apply repeat_Undef_inject_self.
    destruct (eq_nat_dec n 31); subst; try apply repeat_Undef_inject_self.
      unfold inj_ipointer; simpl; repeat econstructor; auto.

    replace (size_chunk_nat chunk) with (length (encode_val chunk v2)).
    apply repeat_Undef_inject_any. apply encode_val_length.
Qed.

(** The identity injection has interesting properties. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  val_inject inject_id v1 v2 <-> Val.lessdef v1 v2.
Proof.
  intros; split; intros.
  inv H; try solve [constructor].
    unfold inject_id in H0. inv H0. rewrite Int.add_zero. constructor.

  inv H; try solve [constructor].
    destruct v2; econstructor. 
      unfold inject_id; reflexivity. 
      rewrite Int.add_zero; auto.
Qed.

Lemma memval_inject_id:
  forall mv, memval_inject inject_id mv mv.
Proof.
  destruct mv; econstructor. unfold inject_id; reflexivity. 
    rewrite Int.add_zero; auto. 
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)

