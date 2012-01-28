(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Equations.
Require Import Axioms.

Definition block : Type := Z.
Definition eq_block := zeq.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Inductive val: Type :=
  | Vundef: val
  | Vint: forall (wz:nat), Int.int wz -> val
  | Vfloat: float -> val
  | Vptr: block -> int32 -> val
  | Vinttoptr: int32 -> val.

Definition zero (wz:nat) := (Int.zero wz).
Definition one (wz:nat) := (Int.one wz).
Definition mone (wz:nat) := (Int.mone wz).

Definition Vzero (wz:nat): val := Vint wz (zero wz).
Definition Vone (wz:nat): val := Vint wz (one wz).
Definition Vmone (wz:nat): val := Vint wz (mone wz).

Definition Vtrue := Vone 0.
Definition Vfalse := Vzero 0.

Definition eq_Vbool (wz:nat) (v v':val) := 
  (v = Vone wz <-> v'= Vtrue) /\
  (v = Vzero wz <-> v'= Vfalse).

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

(* FIXME: Comparision between float and int may not be correct. 
   But we only need the eq to define LLVMgv.eq, which is only used for 
   pointer comparision. *)
Definition eq (v1 v2:val) : bool :=
match v1, v2 with
| Vundef, _ => false
| _, Vundef => false
| Vint wz1 i1, Vint wz2 i2 => zeq (Int.unsigned wz1 i1) (Int.unsigned wz2 i2)
| Vint wz1 i1, Vfloat f2 => 
    zeq (Int.unsigned wz1 i1) (Int.unsigned 31 (Float.intuoffloat f2))
| Vfloat f1, Vint wz2 i2 => 
    zeq (Int.unsigned 31 (Float.intuoffloat f1)) (Int.unsigned wz2 i2)
| Vfloat f1, Vfloat f2 => match (Float.eq_dec f1 f2) with
                          | left _ => true
                          | right _ => false
                          end
| Vptr b1 o1, Vptr b2 o2 => eq_block b1 b2 && 
                            zeq (Int.unsigned 31 o1) (Int.unsigned 31 o2)
| Vinttoptr i1, Vinttoptr i2 => 
    (* FIXME: Should we compare Vinttoptr and Vptr? *)
    zeq (Int.unsigned 31 i1) (Int.unsigned 31 i2)
| _, _ => false
end.

Definition get_wordsize (v : val) : option nat :=
  match v with
  | Vint wz _ => Some wz
  | Vptr _ _ | Vinttoptr _ => 
      (* This is incorrect, size of ptr is configured differently. *)
      Some 31%nat
  | _ => None
  end.

Definition of_bool (b: bool) : val := 
if b then Vtrue else Vfalse.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _ _, Tint => True
  | Vfloat _, Tfloat => True
  | Vptr _ _, Tint => True
  | Vinttoptr _, Tint => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

(** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

Definition is_true (v: val) : Prop :=
  match v with
  | Vint wz n => n <> zero wz
  | Vptr _ _ | Vinttoptr _ => True
  | _ => False
  end.

Definition is_false (v: val) : Prop :=
  match v with
  | Vint wz n => n = zero wz
  | _ => False
  end.

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int_true:
      forall wz n, n <> zero wz -> bool_of_val (Vint wz n) true
  | bool_of_val_int_false:
      forall wz, bool_of_val (Vzero wz) false
  | bool_of_val_ptr:
      forall b ofs, bool_of_val (Vptr b ofs) true
  | bool_of_val_inttoptr:
      forall n, bool_of_val (Vinttoptr n) true.

Definition neg (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.neg wz n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition trunc (v: val) (wz':nat) : val :=
match v with
| Vint wz n => if le_lt_dec wz wz'
               then Vundef
               else Vint wz' (Int.repr wz' (Int.unsigned wz n))
| _ => Vundef
end.

Definition ftrunc (v: val) : val :=
match v with
| Vfloat f => v
| _ => Vundef
end.

Definition intoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint 31 (Float.intoffloat f)
  | _ => Vundef
  end.

Definition intuoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vint 31 (Float.intuoffloat f)
  | _ => Vundef
  end.

Definition floatofint (v: val) : val :=
  match v with
  | Vint 31 n => Vfloat (Float.floatofint n)
  | _ => Vundef
  end.

Definition floatofintu (v: val) : val :=
  match v with
  | Vint 31 n => Vfloat (Float.floatofintu n)
  | _ => Vundef
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint 31 n1, Vint 31 n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.xor wz n (Int.mone wz))
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint wz n => of_bool (Int.eq wz n (zero wz))
  | Vptr _ _ | Vinttoptr _ => Vfalse
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.zero_ext wz nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint wz n => Vint wz (Int.sign_ext wz nbits n)
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vfloat(Float.singleoffloat f)
  | _ => Vundef
  end.

Equations add (v1 v2: val): val :=
add (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  add (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
     Vint wz1 (Int.add wz1 n1 n2);
  add (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
add (Vptr b1 ofs1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  add (Vptr b1 ofs1) (Vint ?(wz2) n2) (left eq_refl) :=
     Vptr b1 (Int.add 31 ofs1 n2);
  add (Vptr b1 ofs1) (Vint ?(wz2) n2) (right p) := Vundef
  };
add (Vint wz1 n1) (Vptr b2 ofs2) with (eq_nat_dec wz1 31) := {
  add (Vint ?(wz1) n1) (Vptr b2 ofs2) (left eq_refl) :=
     Vptr b2 (Int.add 31 ofs2 n1);
  add (Vint wz1 n1) (Vptr b2 ofs2) (right p) := Vundef
  };
add (Vinttoptr n1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  add (Vinttoptr n1) (Vint ?(wz1) n2) (left eq_refl) :=
     Vinttoptr (Int.add 31 n1 n2);
  add (Vinttoptr n1) (Vint wz2 n2) (right p) := Vundef  
  };
add (Vint wz1 n1) (Vinttoptr n2) with (eq_nat_dec wz1 31) := {
  add (Vint wz1 n1) (Vinttoptr n2) (left eq_refl) :=
     Vinttoptr (Int.add wz1 n1 n2);
  add (Vint wz1 n1) (Vinttoptr n2) (right p) := Vundef  
  };
add _ _ := Vundef.

Equations sub (v1 v2: val): val :=
sub (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  sub (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
     Vint wz1 (Int.sub wz1 n1 n2);
  sub (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
sub (Vptr b1 ofs1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  sub (Vptr b1 ofs1) (Vint ?(wz2) n2) (left eq_refl) :=
     Vptr b1 (Int.sub 31 ofs1 n2);
  sub (Vptr b1 ofs1) (Vint ?(wz2) n2) (right p) := Vundef
  };
sub (Vptr b1 ofs1) (Vptr b2 ofs2) := 
  if zeq b1 b2 then Vint 31 (Int.sub 31 ofs1 ofs2) else Vundef;
sub (Vinttoptr n1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  sub (Vinttoptr n1) (Vint ?(wz2) n2) (left eq_refl) :=
     Vinttoptr (Int.sub 31 n1 n2);
  sub (Vinttoptr n1) (Vint ?(wz2) n2) (right p) := Vundef
  };
sub (Vinttoptr n1) (Vinttoptr n2) := Vint 31 (Int.sub 31 n1 n2);
sub _ _ := Vundef.

Equations mul (v1 v2: val): val :=
mul (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  mul (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
     Vint wz1 (Int.mul wz1 n1 n2);
  mul (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
mul _ _ := Vundef.

Equations divs (v1 v2: val): val :=
divs (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  divs (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.eq wz1 n2 (Int.zero wz1) 
    then Vundef 
    else Vint wz1 (Int.divs wz1 n1 n2);
  divs (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
divs _ _ := Vundef.

Equations mods (v1 v2: val): val :=
mods (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  mods (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.eq wz1 n2 (Int.zero wz1) 
    then Vundef 
    else Vint wz1 (Int.mods wz1 n1 n2);
  mods (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
mods _ _ := Vundef.

Equations divu (v1 v2: val): val :=
divu (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  divu (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.eq wz1 n2 (Int.zero wz1) 
    then Vundef 
    else Vint wz1 (Int.divu wz1 n1 n2);
  divu (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
divu _ _ := Vundef.

Equations modu (v1 v2: val): val :=
modu (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  modu (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.eq wz1 n2 (Int.zero wz1) 
    then Vundef 
    else Vint wz1 (Int.modu wz1 n1 n2);
  modu (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
modu _ _ := Vundef.

Equations and (v1 v2: val): val :=
and (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  and (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    Vint wz1 (Int.and wz1 n1 n2);
  and (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
and _ _ := Vundef.

Equations or (v1 v2: val): val :=
or (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  or (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    Vint wz1 (Int.or wz1 n1 n2);
  or (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
or _ _ := Vundef.

Equations xor (v1 v2: val): val :=
xor (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  xor (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    Vint wz1 (Int.xor wz1 n1 n2);
  xor (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
xor _ _ := Vundef.

Equations shl (v1 v2: val): val :=
shl (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  shl (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.shl wz1 n1 n2)
    else Vundef;
  shl (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
shl _ _ := Vundef.

Equations shr (v1 v2: val): val :=
shr (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  shr (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.shr wz1 n1 n2)
    else Vundef;
  shr (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
shr _ _ := Vundef.

Equations shr_carry (v1 v2: val): val :=
shr_carry (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  shr_carry (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.shr_carry wz1 n1 n2)
    else Vundef;
  shr_carry (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
shr_carry _ _ := Vundef.

Equations shrx (v1 v2: val): val :=
shrx (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  shrx (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.shrx wz1 n1 n2)
    else Vundef;
  shrx (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
shrx _ _ := Vundef.

Equations shru (v1 v2: val): val :=
shru (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  shru (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.shru wz1 n1 n2)
    else Vundef;
  shru (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
shru _ _ := Vundef.

(*
Record R (wz:nat) := mkR { a : nat }.

Inductive D : Prop :=
  | C : forall (wz:nat), wz <> 0%nat -> R wz -> D
  .

Definition f (wz:nat) (H:wz <> 0%nat) (r1 r2 r3: R wz) : D := 
match wz with
| O => C wz H r1
| S O => C wz H r2
| _ => C wz H r3
end. 

Equations test (d d': D) : D :=
test (C wz wz_isnt_zero r) (C wz' wz_isnt_zero' r') with (eq_nat_dec wz wz') := {
  test (C wz wz_isnt_zero r) (C ?(wz) wz_isnt_zero' r') (left eq_refl) := f wz wz_isnt_zero r r' r';
  test (C wz wz_isnt_zero r) (C wz' wz_isnt_zero' r') (right p) := (C wz wz_isnt_zero r)
  }.

Equations test2 (d: D) (wz':nat) (r' r'': R wz'): D :=
test2 (C wz wz_isnt_zero r) wz' r' r'' with (eq_nat_dec wz wz') := {
  test2 (C wz wz_isnt_zero r) ?(wz) r' r'' (left eq_refl) :=f wz wz_isnt_zero r r' r'';
  test2 (C wz wz_isnt_zero r) wz' r' r'' _ := (C wz wz_isnt_zero r)
  }.

Equations rolm (v: val) (wz:nat) (amount mask: Int.int wz): val :=
rolm (Vint wz1 n1) wz0 amount mask <= (eq_nat_dec wz0 wz1) => {
  rolm (Vint wz1 n1) ?(wz1) amount mask (left eq_refl) :=
    Vint wz1 (Int.rolm wz1 n1 amount mask);
  rolm _ _ _ _ (right p) := Vundef
  };
rolm _ _ _ _ := Vundef.

Equations rolm (v: val) (wz:nat) (amount mask: Int.int wz): val :=
rolm (Vint wz1 wz_not_zero1 n1) wz0 amount mask <= (eq_nat_dec wz1 wz0) => {
  rolm (Vint wz1 wz_not_zero1 n1) ?(wz1) amount mask (left eq_refl) :=
    Vint wz1 wz_not_zero1 (Int.rolm wz1 wz_not_zero1 n1 amount mask);
  rolm _ _ _ _ (right p) := Vundef
  };
rolm _ _ _ _ := Vundef.

Equations rolm (v: val) (wz:nat) (wz_not_zero:wz <> 0%nat) (amount mask: Int.int wz): val :=
rolm (Vint wz1 wz_not_zero1 n1) wz0 wz_not_zero0 amount mask with (eq_nat_dec wz1 wz0) := {
  rolm (Vint wz1 wz_not_zero1 n1) ?(wz1) wz_not_zero0 amount0 mask (left eq_refl) :=
    Vint wz1 wz_not_zero1 (Int.rolm wz1 wz_not_zero1 n1 amount0 mask);
  rolm (Vint wz1 wz_not_zero1 n1) wz0 wz_not_zero0 amount mask (right p) := Vundef  
  };
rolm _ _ _ _ _ := Vundef.
*)

Definition rolm (v: val) (amount mask: int32): val :=
  match v with
  | Vint 31 n => Vint 31 (Int.rolm 31 n amount mask)
  | _ => Vundef
  end.

Equations ror (v1 v2: val): val :=
ror (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  ror (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    if Int.ltu wz1 n2 (Int.iwordsize wz1)
    then Vint wz1 (Int.ror wz1 n1 n2)
    else Vundef;
  ror (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
ror _ _ := Vundef.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition modf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.rem f1 f2)
  | _, _ => Vundef
  end.

Definition cmp_mismatch (c: comparison): val :=
  match c with
  | Ceq => Vfalse
  | Cne => Vtrue
  | _   => Vundef
  end.

Equations cmp (c: comparison) (v1 v2: val): val :=
cmp c (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  cmp c (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    of_bool (Int.cmp wz1 c n1 n2);
  cmp c (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
cmp c (Vint wz1 n1) (Vptr b2 ofs2) with (eq_nat_dec wz1 31) := {
  cmp c (Vint ?(wz1) n1) (Vptr b2 ofs2) (left eq_refl) :=
    if Int.eq 31 n1 (Int.zero 31) then cmp_mismatch c else Vundef;
  cmp c (Vint wz1 n1) (Vptr b2 ofs2) (right p) := Vundef
  };
cmp c (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  if zeq b1 b2
  then of_bool (Int.cmp 31 c ofs1 ofs2)
  else cmp_mismatch c;
cmp c (Vptr b1 ofs1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  cmp c (Vptr b1 ofs1) (Vint ?(wz2) n2) (left eq_refl) :=
    if Int.eq 31 n2 (Int.zero 31) then cmp_mismatch c else Vundef;
  cmp c (Vptr b1 ofs1) (Vint wz2 n2) (right p) := Vundef
  };
cmp c (Vint wz1 n1) (Vinttoptr n2) with (eq_nat_dec wz1 31) := {
  cmp c (Vint wz1 n1) (Vinttoptr n2) (left eq_refl) := Vundef;
  cmp c (Vint wz1 n1) (Vinttoptr n2) (right p) := Vundef  
  };
cmp c (Vinttoptr n1) (Vinttoptr n2) := of_bool (Int.cmp 31 c n1 n2);
cmp c (Vinttoptr n1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  cmp c (Vinttoptr n1) (Vint ?(wz2) n2) (left eq_refl) := Vundef;
  cmp c (Vinttoptr n1) (Vint wz2 n2) (right p) := Vundef  
  };
(* FIXME: Vptr and Vinttoptr are not compariable. *)
cmp _ _ _ := Vundef.

Equations cmpu (c: comparison) (v1 v2: val): val :=
cmpu c (Vint wz1 n1) (Vint wz2 n2) with (eq_nat_dec wz1 wz2) := {
  cmpu c (Vint wz1 n1) (Vint ?(wz1) n2) (left eq_refl) :=
    of_bool (Int.cmpu wz1 c n1 n2);
  cmpu c (Vint wz1 n1) (Vint wz2 n2) (right p) := Vundef  
  };
cmpu c (Vint wz1 n1) (Vptr b2 ofs2) with (eq_nat_dec wz1 31) := {
  cmpu c (Vint ?(wz1) n1) (Vptr b2 ofs2) (left eq_refl) :=
    if Int.eq 31 n1 (Int.zero 31) then cmp_mismatch c else Vundef;
  cmpu c (Vint wz1 n1) (Vptr b2 ofs2) (right p) := Vundef
  };
cmpu c (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  if zeq b1 b2
  then of_bool (Int.cmpu 31 c ofs1 ofs2)
  else cmp_mismatch c;
cmpu c (Vptr b1 ofs1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  cmpu c (Vptr b1 ofs1) (Vint ?(wz2) n2) (left eq_refl) :=
    if Int.eq 31 n2 (Int.zero 31) then cmp_mismatch c else Vundef;
  cmpu c (Vptr b1 ofs1) (Vint wz2 n2) (right p) := Vundef
  };
cmpu c (Vint wz1 n1) (Vinttoptr n2) with (eq_nat_dec wz1 31) := {
  cmpu c (Vint wz1 n1) (Vinttoptr n2) (left eq_refl) := Vundef;
  cmpu c (Vint wz1 n1) (Vinttoptr n2) (right p) := Vundef  
  };
cmpu c (Vinttoptr n1) (Vinttoptr n2) := of_bool (Int.cmpu 31 c n1 n2);
cmpu c (Vinttoptr n1) (Vint wz2 n2) with (eq_nat_dec wz2 31) := {
  cmpu c (Vinttoptr n1) (Vint ?(wz2) n2) (left eq_refl) := Vundef;
  cmpu c (Vinttoptr n1) (Vint wz2 n2) (right p) := Vundef  
  };
(* FIXME: Vptr and Vinttoptr are not compariable. *)
cmpu _ _ _ := Vundef.

Definition cmpf (c: comparison) (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => of_bool (Float.cmp c f1 f2)
  | _, _ => Vundef
  end.

(** * Tacticals for Equations *)

Ltac simpl_misc :=
  (match goal with
  | [ |- context [Vtrue] ] => unfold Vtrue; unfold Vone; unfold one
  | [ |- context [Vfalse] ] => unfold Vfalse; unfold Vzero; unfold zero
  | [ |- context [Vone] ] => unfold Vone; unfold one
  | [ |- context [Vmone] ] => unfold Vmone; unfold mone
  | [ |- context [Vzero] ] => unfold Vzero; unfold zero
  | [ |- context [ Logic.eq_sym ?e ] ] =>
  generalize (proof_irr e eq_refl);
  intro; subst; simpl
  | [ H : get_wordsize (Vint ?wz _) = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  | [ H : get_wordsize (Vone ?wz _) = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  | [ H : get_wordsize (Vmone ?wz _) = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  | [ H : get_wordsize (Vzero ?wz _) = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  | [ H : get_wordsize Vtrue = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  | [ H : get_wordsize Vfalse = Some ?wz0 |- _ ] =>
    simpl in H; inversion H; subst
  end).

Ltac simpl_add :=
  (match goal with
  | [ |- context [add Vundef _] ] => 
      rewrite add_equation_1
  | [ |- context [add (Vint ?wz ?i) Vundef] ] => 
      rewrite add_equation_2

  | [ |- context [add (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite add_equation_3;
      unfold add_obligation_3;
      unfold add_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [add_obligation_1] ] =>
      unfold add_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [add (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite add_equation_4

  | [ |- context [add (Vint ?wz ?i) (Vptr _ _)] ] =>
    rewrite add_equation_5;
    unfold add_obligation_6;
    unfold add_obligation_5;
    destruct (eq_nat_dec wz 31); subst
  | [ |- context [add_obligation_4] ] =>
    unfold add_obligation_4;
    unfold solution_left;
    unfold eq_rect_r;
    unfold eq_rect;
    simpl

  | [ |- context [add (Vint ?wz ?i) (Vinttoptr ?i0) ] ] =>
  rewrite add_equation_6;
  unfold add_obligation_9;
  unfold add_obligation_8;
  unfold add_obligation_7;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [add (Vfloat ?f) _] ] =>
      rewrite add_equation_7
  | [ |- context [add (Vptr ?b ?i) Vundef] ] =>
      rewrite add_equation_8

  | [ |- context [add (Vptr _ _) (Vint ?wz ?i)] ] =>
  rewrite add_equation_9;
  unfold add_obligation_13;
  unfold add_obligation_12;
  destruct (eq_nat_dec wz 31); subst
  | [ |- context [add_obligation_8] ] =>
  unfold add_obligation_8;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  simpl

  | [ |- context [add (Vptr ?b ?i) (Vfloat ?f)] ] =>
      rewrite add_equation_10
  | [ |- context [add (Vptr ?b ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite add_equation_11

  | [ |- context [add (Vptr ?b ?i) (Vinttoptr ?i0)] ] =>
      rewrite add_equation_12
  | [ |- context [add (Vinttoptr ?i) Vundef] ] => 
      rewrite add_equation_13

  | [ |- context [add (Vinttoptr ?i0) (Vint ?wz ?i)] ] =>
  rewrite add_equation_14;
  unfold add_obligation_17;
  unfold add_obligation_16;
  unfold add_obligation_15;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [add (Vinttoptr ?i) (Vfloat ?f)] ] => 
      rewrite add_equation_15

  | [ |- context [add (Vinttoptr ?i) (Vptr ?b ?i0)] ] => 
      rewrite add_equation_16

  | [ |- context [add (Vinttoptr ?i) (Vinttoptr ?i0)] ] => 
      rewrite add_equation_17

  | [ |- context [add_obligation_11] ] =>
      unfold add_obligation_11, solution_left, eq_rect_r, eq_rect

  end).

Ltac ctx_contradiction :=
  match goal with
  | [ H : eq_nat_dec ?wz ?wz = in_right |- _ ] =>
    let e := fresh "e" in
    let n := fresh "n" in
    destruct (eq_nat_dec wz wz) as [e | n]; try solve
      [inversion H | contradiction n; auto]
  | [ H : eq_nat_dec ?wz0 ?wz = in_right, 
      H' : Some ?wz = Some ?wz0 
      |- _ ] =>
    let e := fresh "e" in
    let n := fresh "n" in
    inversion H'; subst;
    destruct (eq_nat_dec wz0 wz0) as [e | n]; try solve
      [inversion H | contradiction n; auto]
  | [ H : eq_nat_dec ?wz0 ?wz = in_right, 
      H' : Some ?wz0 = Some ?wz 
      |- _ ] =>
    let e := fresh "e" in
    let n := fresh "n" in
    inversion H'; subst;
    destruct (eq_nat_dec wz0 wz0) as [e | n]; try solve
      [inversion H | contradiction n; auto]
  | [ H : None = Some _ |- _] => inversion H
  | [ H : Some _ = None |- _] => inversion H
  | [ H : ?wz ≠ ?wz |- _] => contradiction H; auto
  | [ H : ?wz ≠ ?wz0, 
      H' : Some ?wz = Some ?wz0
      |- _] => 
    inversion H'; subst;
    contradiction H; auto
  | [ H : ?wz ≠ ?wz0, 
      H' : Some ?wz0 = Some ?wz
      |- _] => 
    inversion H'; subst;
    contradiction H; auto
  | [ H : ?wz ≠ ?wz0, 
      H' : get_wordsize (Vint ?wz _) = Some ?wz0
      |- _] => 
    simpl in H'; inversion H'; subst;
    contradiction H; auto
  | [ H : ?wz ≠ ?wz0, 
      H' : get_wordsize (Vint ?wz0 _) = Some ?wz
      |- _] => 
    simpl in H'; inversion H'; subst;
    contradiction H; auto
  | [ H : ?wz ≠ 31%nat, 
      H' : get_wordsize (Vptr _ _) = Some ?wz
      |- _] => 
    simpl in H'; inversion H'; subst;
    contradiction H; auto
  | [ H : ?wz ≠ ?wz |- _] => contradict H; auto
  end.

Ltac simpl_sub :=
  try (match goal with
  | [ |- context [sub Vundef _] ] => 
      rewrite sub_equation_1
  | [ |- context [sub (Vint ?wz ?i) Vundef] ] => 
      rewrite sub_equation_2

  | [ |- context [sub (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite sub_equation_3;
      unfold sub_obligation_3;
      unfold sub_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [sub_obligation_1] ] =>
      unfold sub_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [sub (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite sub_equation_4
  | [ |- context [sub (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite sub_equation_5
  | [ |- context [sub (Vint ?wz ?i) (Vinttoptr ?i0)] ] =>
      rewrite sub_equation_6
  | [ |- context [sub (Vfloat ?f) _] ] =>
      rewrite sub_equation_7
  | [ |- context [sub (Vptr ?b ?i) Vundef] ] =>
      rewrite sub_equation_8

  | [ |- context [sub (Vptr ?b ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite sub_equation_9;
      unfold sub_obligation_7;
      unfold sub_obligation_6;
      unfold sub_obligation_5;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      destruct (eq_nat_dec wz0 31); subst
  | [ |- context [sub_obligation_5] ] =>
      unfold sub_obligation_5;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [sub (Vptr ?b ?i) (Vfloat ?f)] ] =>
      rewrite sub_equation_10
  | [ |- context [sub (Vptr ?b ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite sub_equation_11
  | [ |- context [sub (Vptr ?b ?i) (Vinttoptr ?i0)] ] =>
      rewrite sub_equation_12
  | [ |- context [sub (Vinttoptr ?i) Vundef] ] =>
      rewrite sub_equation_13

  | [ |- context [sub (Vinttoptr ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite sub_equation_14;
      unfold sub_obligation_11;
      unfold sub_obligation_10;
      unfold sub_obligation_9;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      destruct (eq_nat_dec wz0 31); subst

  | [ |- context [sub (Vinttoptr ?i) (Vfloat ?f)] ] =>
      rewrite sub_equation_15
  | [ |- context [sub (Vinttoptr ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite sub_equation_16
  | [ |- context [sub (Vinttoptr ?i) (Vinttoptr ?i0)] ] =>
      rewrite sub_equation_17

  end).

Ltac simpl_mul :=
  (match goal with
  | [ |- context [mul Vundef _] ] => 
      rewrite mul_equation_1
  | [ |- context [mul (Vint ?wz ?i) Vundef] ] => 
      rewrite mul_equation_2

  | [ |- context [mul (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite mul_equation_3;
      unfold mul_obligation_3;
      unfold mul_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [mul_obligation_1] ] =>
      unfold mul_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [mul (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite mul_equation_4
  | [ |- context [mul (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite mul_equation_5
  | [ |- context [mul (Vfloat ?f) _] ] =>
      rewrite mul_equation_6
  | [ |- context [mul (Vptr ?b ?i) _] ] =>
      rewrite mul_equation_7
  end).

Ltac simpl_divs :=
  (match goal with
  | [ |- context [divs Vundef _] ] => 
      rewrite divs_equation_1
  | [ |- context [divs (Vint ?wz ?i) Vundef] ] => 
      rewrite divs_equation_2

  | [ |- context [divs (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite divs_equation_3;
      unfold divs_obligation_3;
      unfold divs_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [divs_obligation_1] ] =>
      unfold divs_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [divs (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite divs_equation_4
  | [ |- context [divs (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite divs_equation_5
  | [ |- context [divs (Vfloat ?f) _] ] =>
      rewrite divs_equation_6
  | [ |- context [divs (Vptr ?b ?i) _] ] =>
      rewrite divs_equation_7
  end).

Ltac simpl_divu :=
  (match goal with
  | [ |- context [divu Vundef _] ] => 
      rewrite divu_equation_1
  | [ |- context [divu (Vint ?wz ?i) Vundef] ] => 
      rewrite divu_equation_2

  | [ |- context [divu (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite divu_equation_3;
      unfold divu_obligation_3;
      unfold divu_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [divu_obligation_1] ] =>
      unfold divu_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [divu (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite divu_equation_4
  | [ |- context [divu (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite divu_equation_5
  | [ |- context [divu (Vfloat ?f) _] ] =>
      rewrite divu_equation_6
  | [ |- context [divu (Vptr ?b ?i) _] ] =>
      rewrite divu_equation_7
  end).

Ltac simpl_mods :=
  (match goal with
  | [ |- context [mods Vundef _] ] => 
      rewrite mods_equation_1
  | [ |- context [mods (Vint ?wz ?i) Vundef] ] => 
      rewrite mods_equation_2

  | [ |- context [mods (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite mods_equation_3;
      unfold mods_obligation_3;
      unfold mods_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [mods_obligation_1] ] =>
      unfold mods_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [mods (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite mods_equation_4
  | [ |- context [mods (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite mods_equation_5
  | [ |- context [mods (Vfloat ?f) _] ] =>
      rewrite mods_equation_6
  | [ |- context [mods (Vptr ?b ?i) _] ] =>
      rewrite mods_equation_7
  end).

Ltac simpl_modu :=
  (match goal with
  | [ |- context [modu Vundef _] ] => 
      rewrite modu_equation_1
  | [ |- context [modu (Vint ?wz ?i) Vundef] ] => 
      rewrite modu_equation_2

  | [ |- context [modu (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite modu_equation_3;
      unfold modu_obligation_3;
      unfold modu_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [modu_obligation_1] ] =>
      unfold modu_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [modu (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite modu_equation_4
  | [ |- context [modu (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite modu_equation_5
  | [ |- context [modu (Vfloat ?f) _] ] =>
      rewrite modu_equation_6
  | [ |- context [modu (Vptr ?b ?i) _] ] =>
      rewrite modu_equation_7
  end).

Ltac simpl_shl :=
  (match goal with
  | [ |- context [shl Vundef _] ] => 
      rewrite shl_equation_1
  | [ |- context [shl (Vint ?wz ?i) Vundef] ] => 
      rewrite shl_equation_2

  | [ |- context [shl (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite shl_equation_3;
      unfold shl_obligation_3;
      unfold shl_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [shl_obligation_1] ] =>
      unfold shl_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [shl (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite shl_equation_4
  | [ |- context [shl (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite shl_equation_5
  | [ |- context [shl (Vfloat ?f) _] ] =>
      rewrite shl_equation_6
  | [ |- context [shl (Vptr ?b ?i) _] ] =>
      rewrite shl_equation_7
  end).

Ltac simpl_shr :=
  (match goal with
  | [ |- context [shr Vundef _] ] => 
      rewrite shr_equation_1
  | [ |- context [shr (Vint ?wz ?i) Vundef] ] => 
      rewrite shr_equation_2

  | [ |- context [shr (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite shr_equation_3;
      unfold shr_obligation_3;
      unfold shr_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [shr_obligation_1] ] =>
      unfold shr_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [shr (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite shr_equation_4
  | [ |- context [shr (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite shr_equation_5
  | [ |- context [shr (Vfloat ?f) _] ] =>
      rewrite shr_equation_6
  | [ |- context [shr (Vptr ?b ?i) _] ] =>
      rewrite shr_equation_7
  end).


Ltac simpl_shr_carry :=
  (match goal with
  | [ |- context [shr_carry Vundef _] ] => 
      rewrite shr_carry_equation_1
  | [ |- context [shr_carry (Vint ?wz ?i) Vundef] ] => 
      rewrite shr_carry_equation_2

  | [ |- context [shr_carry (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite shr_carry_equation_3;
      unfold shr_carry_obligation_3;
      unfold shr_carry_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [shr_carry_obligation_1] ] =>
      unfold shr_carry_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [shr_carry (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite shr_carry_equation_4
  | [ |- context [shr_carry (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite shr_carry_equation_5
  | [ |- context [shr_carry (Vfloat ?f) _] ] =>
      rewrite shr_carry_equation_6
  | [ |- context [shr_carry (Vptr ?b ?i) _] ] =>
      rewrite shr_carry_equation_7
  end).

Ltac simpl_shrx :=
  (match goal with
  | [ |- context [shrx Vundef _] ] => 
      rewrite shrx_equation_1
  | [ |- context [shrx (Vint ?wz ?i) Vundef] ] => 
      rewrite shrx_equation_2

  | [ |- context [shrx (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite shrx_equation_3;
      unfold shrx_obligation_3;
      unfold shrx_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [shrx_obligation_1] ] =>
      unfold shrx_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [shrx (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite shrx_equation_4
  | [ |- context [shrx (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite shrx_equation_5
  | [ |- context [shrx (Vfloat ?f) _] ] =>
      rewrite shrx_equation_6
  | [ |- context [shrx (Vptr ?b ?i) _] ] =>
      rewrite shrx_equation_7
  end).

Ltac simpl_shru :=
  (match goal with
  | [ |- context [shru Vundef _] ] => 
      rewrite shru_equation_1
  | [ |- context [shru (Vint ?wz ?i) Vundef] ] => 
      rewrite shru_equation_2

  | [ |- context [shru (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite shru_equation_3;
      unfold shru_obligation_3;
      unfold shru_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [shru_obligation_1] ] =>
      unfold shru_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [shru (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite shru_equation_4
  | [ |- context [shru (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite shru_equation_5
  | [ |- context [shru (Vfloat ?f) _] ] =>
      rewrite shru_equation_6
  | [ |- context [shru (Vptr ?b ?i) _] ] =>
      rewrite shru_equation_7
  end).

Ltac simpl_ror :=
  (match goal with
  | [ |- context [ror Vundef _] ] => 
      rewrite ror_equation_1
  | [ |- context [ror (Vint ?wz ?i) Vundef] ] => 
      rewrite ror_equation_2

  | [ |- context [ror (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite ror_equation_3;
      unfold ror_obligation_3;
      unfold ror_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [ror_obligation_1] ] =>
      unfold ror_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [ror (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite ror_equation_4
  | [ |- context [ror (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite ror_equation_5
  | [ |- context [ror (Vfloat ?f) _] ] =>
      rewrite ror_equation_6
  | [ |- context [ror (Vptr ?b ?i) _] ] =>
      rewrite ror_equation_7
  end).

Ltac simpl_and :=
  (match goal with
  | [ |- context [and Vundef _] ] => 
      rewrite and_equation_1
  | [ |- context [and (Vint ?wz ?i) Vundef] ] => 
      rewrite and_equation_2

  | [ |- context [and (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite and_equation_3;
      unfold and_obligation_3;
      unfold and_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [and_obligation_1] ] =>
      unfold and_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [and (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite and_equation_4
  | [ |- context [and (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite and_equation_5
  | [ |- context [and (Vfloat ?f) _] ] =>
      rewrite and_equation_6
  | [ |- context [shr (Vptr ?b ?i) _] ] =>
      rewrite and_equation_7
  end).

Ltac simpl_or :=
  (match goal with
  | [ |- context [or Vundef _] ] => 
      rewrite or_equation_1
  | [ |- context [or (Vint ?wz ?i) Vundef] ] => 
      rewrite or_equation_2

  | [ |- context [or (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite or_equation_3;
      unfold or_obligation_3;
      unfold or_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [or_obligation_1] ] =>
      unfold or_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [or (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite or_equation_4
  | [ |- context [or (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite or_equation_5
  | [ |- context [or (Vfloat ?f) _] ] =>
      rewrite or_equation_6
  | [ |- context [or (Vptr ?b ?i) _] ] =>
      rewrite or_equation_7
  end).

Ltac simpl_xor :=
  (match goal with
  | [ |- context [xor Vundef _] ] => 
      rewrite xor_equation_1
  | [ |- context [xor (Vint ?wz ?i) Vundef] ] => 
      rewrite xor_equation_2

  | [ |- context [xor (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite xor_equation_3;
      unfold xor_obligation_3;
      unfold xor_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [xor_obligation_1] ] =>
      unfold xor_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [xor (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite xor_equation_4
  | [ |- context [xor (Vint ?wz ?i) (Vptr ?b ?i0)] ] =>
      rewrite xor_equation_5
  | [ |- context [xor (Vfloat ?f) _] ] =>
      rewrite xor_equation_6
  | [ |- context [xor (Vptr ?b ?i) _] ] =>
      rewrite xor_equation_7
  end).

Ltac simpl_cmp :=
  (match goal with
  | [ |- context [cmp _ Vundef _] ] => 
      rewrite cmp_equation_1
  | [ |- context [cmp _ (Vint ?wz ?i) Vundef] ] => 
      rewrite cmp_equation_2

  | [ |- context [cmp _ (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite cmp_equation_3;
      unfold cmp_obligation_3;
      unfold cmp_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [cmp_obligation_1] ] =>
      unfold cmp_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [cmp _ (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite add_equation_4

  | [ |- context [cmp _ (Vint ?wz ?i) (Vptr _ _)] ] =>
    rewrite cmp_equation_5;
    unfold cmp_obligation_6;
    unfold cmp_obligation_5;
    destruct (eq_nat_dec wz 31); subst
  | [ |- context [cmp_obligation_4] ] =>
    unfold cmp_obligation_4;
    unfold solution_left;
    unfold eq_rect_r;
    unfold eq_rect;
    simpl

  | [ |- context [cmp _ (Vint ?wz ?i) (Vinttoptr ?i0)] ] =>
  rewrite cmp_equation_6;
  unfold cmp_obligation_9;
  unfold cmp_obligation_8;
  unfold cmp_obligation_7;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [cmp _ (Vfloat ?f) _] ] =>
      rewrite cmp_equation_7
  | [ |- context [cmp _ (Vptr ?b ?i) Vundef] ] =>
      rewrite cmp_equation_8

  | [ |- context [cmp _ (Vptr _ _) (Vint ?wz ?i)] ] =>
  rewrite cmp_equation_9;
  unfold cmp_obligation_13;
  unfold cmp_obligation_12;
  unfold cmp_obligation_11;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [cmp_obligation_8] ] =>
  unfold cmp_obligation_8;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  simpl

  | [ |- context [cmp _ (Vptr ?b ?i) (Vfloat ?f)] ] =>
      rewrite cmp_equation_10
  | [ |- context [cmp _ (Vptr ?b ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite cmp_equation_11
  | [ |- context [cmp _ (Vptr ?b ?i) (Vinttoptr ?i0)] ] =>
      rewrite cmp_equation_12
  | [ |- context [cmp _ (Vinttoptr ?i) Vundef] ] =>
      rewrite cmp_equation_13

  | [ |- context [cmp _ (Vinttoptr ?i) (Vint ?wz0 ?i0)] ] =>
  rewrite cmp_equation_14;
  unfold cmp_obligation_17;
  unfold cmp_obligation_16;
  unfold cmp_obligation_15;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz0 31); subst

  | [ |- context [cmp _ (Vinttoptr ?i) (Vfloat ?f0)] ] =>
      rewrite cmp_equation_15
  | [ |- context [cmp _ (Vinttoptr ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite cmp_equation_16
  | [ |- context [cmp _ (Vinttoptr ?i) (Vinttoptr ?i0)] ] =>
      rewrite cmp_equation_17

  end).

Ltac simpl_cmpu :=
  (match goal with
  | [ |- context [cmpu _ Vundef _] ] => 
      rewrite cmpu_equation_1
  | [ |- context [cmpu _ (Vint ?wz ?i) Vundef] ] => 
      rewrite cmpu_equation_2

  | [ |- context [cmpu _ (Vint ?wz ?i) (Vint ?wz0 ?i0)] ] =>
      rewrite cmpu_equation_3;
      unfold cmpu_obligation_3;
      unfold cmpu_obligation_2;
      destruct (eq_nat_dec wz wz0); subst
  | [ |- context [cmpu_obligation_1] ] =>
      unfold cmpu_obligation_1;
      unfold solution_left;
      unfold eq_rect_r;
      unfold eq_rect;
      simpl

  | [ |- context [cmpu _ (Vint ?wz ?i) (Vfloat ?f)] ] =>
      rewrite add_equation_4

  | [ |- context [cmpu _ (Vint ?wz ?i) (Vptr _ _)] ] =>
    rewrite cmpu_equation_5;
    unfold cmpu_obligation_6;
    unfold cmpu_obligation_5;
    destruct (eq_nat_dec wz 31); subst
  | [ |- context [cmpu_obligation_4] ] =>
    unfold cmpu_obligation_4;
    unfold solution_left;
    unfold eq_rect_r;
    unfold eq_rect;
    simpl

  | [ |- context [cmpu _ (Vint ?wz ?i) (Vinttoptr ?i0)] ] =>
  rewrite cmpu_equation_6;
  unfold cmpu_obligation_9;
  unfold cmpu_obligation_8;
  unfold cmpu_obligation_7;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [cmpu _ (Vfloat ?f) _] ] =>
      rewrite cmpu_equation_7
  | [ |- context [cmpu _ (Vptr ?b ?i) Vundef] ] =>
      rewrite cmpu_equation_8

  | [ |- context [cmpu _ (Vptr _ _) (Vint ?wz ?i)] ] =>
  rewrite cmpu_equation_9;
  unfold cmpu_obligation_13;
  unfold cmpu_obligation_12;
  unfold cmpu_obligation_11;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz 31); subst

  | [ |- context [cmpu_obligation_8] ] =>
  unfold cmpu_obligation_8;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  simpl

  | [ |- context [cmpu _ (Vptr ?b ?i) (Vfloat ?f)] ] =>
      rewrite cmpu_equation_10
  | [ |- context [cmpu _ (Vptr ?b ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite cmpu_equation_11
  | [ |- context [cmpu _ (Vptr ?b ?i) (Vinttoptr ?i0)] ] =>
      rewrite cmpu_equation_12
  | [ |- context [cmpu _ (Vinttoptr ?i) Vundef] ] =>
      rewrite cmpu_equation_13

  | [ |- context [cmpu _ (Vinttoptr ?i) (Vint ?wz0 ?i0)] ] =>
  rewrite cmpu_equation_14;
  unfold cmpu_obligation_17;
  unfold cmpu_obligation_16;
  unfold cmpu_obligation_15;
  unfold solution_left;
  unfold eq_rect_r;
  unfold eq_rect;
  destruct (eq_nat_dec wz0 31); subst

  | [ |- context [cmpu _ (Vinttoptr ?i) (Vfloat ?f0)] ] =>
      rewrite cmpu_equation_15
  | [ |- context [cmpu _ (Vinttoptr ?i) (Vptr ?b0 ?i0)] ] =>
      rewrite cmpu_equation_16
  | [ |- context [cmpu _ (Vinttoptr ?i) (Vinttoptr ?i0)] ] =>
      rewrite cmpu_equation_17

  end).

Ltac simpl_equations := repeat 
  (simpl || simpl_misc || 
   simpl_add || simpl_sub || 
   simpl_mul || simpl_divs || simpl_mods || simpl_divu || simpl_modu ||
   simpl_shl || simpl_shr || simpl_shr_carry || simpl_shrx || simpl_shru || 
   simpl_ror || simpl_and || simpl_or || simpl_xor ||
   simpl_cmp || simpl_cmpu ).

Ltac simpl_auto_equations := 
  simpl_equations; try solve [auto | ctx_contradiction].


(** [load_result] is used in the memory model (library [Mem])
  to post-process the results of a memory read.  For instance,
  consider storing the integer value [0xFFF] on 1 byte at a
  given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension
  is performed and [0xFFFFFFFF] is returned.   Type mismatches
  (e.g. reading back a float as a [Mint32]) read back as [Vundef]. *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint wz1, Vint wz2 n => Vint wz1 (Int.repr wz1 (Int.unsigned wz2 n))
  | Mint wz, Vptr b ofs => if eq_nat_dec wz 31 then Vptr b ofs else Vundef
  | Mint wz, Vinttoptr i => if eq_nat_dec wz 31 then Vinttoptr i else Vundef
  | Mfloat32, Vfloat f => Vfloat(Float.singleoffloat f)
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.

(** Theorems on arithmetic operations. *)

Section ArithOperations.

Variable x : val.

Hypothesis x_is_int : get_wordsize x = Some 31%nat.

Theorem cast8unsigned_and:
  zero_ext 8 x = and x (Vint 31 (Int.repr 31 255)).
Proof.
  destruct x; simpl; auto.
  funelim (and (Vint wz i) (Vint 31 (Int.repr 31 255))).
    decEq. change 255 with (two_p 8 - 1). apply Int.zero_ext_and. vm_compute; auto.
    inversion x_is_int; subst. contradiction f; auto.
Qed.

Theorem cast16unsigned_and:
  zero_ext 16 x = and x (Vint 31 (Int.repr 31 65535)).
Proof.
  destruct x; simpl; auto. 
  funelim (and (Vint wz i) (Vint 31 (Int.repr 31 65535))).
    decEq. change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. vm_compute; auto.
    inversion x_is_int; subst. contradiction f; auto.
Qed.

End ArithOperations.

Theorem istrue_not_isfalse:
  forall v, is_false v -> is_true (notbool v).
Proof.
  destruct v; simpl; try contradiction.
  intros. subst i. simpl. apply Int.one_not_zero.
Qed.

Theorem isfalse_not_istrue:
  forall v, is_true v -> is_false (notbool v).
Proof.
  destruct v; simpl; try contradiction; auto.
  intros. generalize (Int.eq_spec wz i (zero wz)).
  case (Int.eq wz i (zero wz)); intro; simpl; auto.
    contradiction. 
Qed.

Theorem bool_of_true_val:
  forall v, is_true v -> bool_of_val v true.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  constructor; auto. constructor. constructor.
Qed.

Theorem bool_of_true_val2:
  forall v, bool_of_val v true -> is_true v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_true_val_inv:
  forall v b, is_true v -> bool_of_val v b -> b = true.
Proof.
  intros. inversion H0; subst v b; simpl in H; auto. 
Qed.

Theorem bool_of_false_val:
  forall v, is_false v -> bool_of_val v false.
Proof.
  intro. destruct v; simpl; intros; try contradiction.
  subst i;  constructor.
Qed.

Theorem bool_of_false_val2:
  forall v, bool_of_val v false -> is_false v.
Proof.
  intros. inversion H; simpl; auto.
Qed.

Theorem bool_of_false_val_inv:
  forall v b, is_false v -> bool_of_val v b -> b = false.
Proof.
  intros. inversion H0; subst v b; simpl in H.
  congruence. auto. contradiction. contradiction.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto. 
  case (Int.eq wz i (zero wz)); reflexivity.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl_auto_equations;
    decEq; apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations;
    try solve [
      decEq; rewrite Int.add_assoc; auto |
      decEq; rewrite Int.add_assoc; rewrite (Int.add_commut 31 i i0); auto |
      decEq; rewrite Int.add_assoc; rewrite (Int.add_commut 31 i i1); 
        rewrite <- Int.add_assoc; auto
    ].
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc.
  apply (add_commut (add x z) y).
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc. 
  rewrite add_permut. symmetry. apply (add_assoc x z (add y t)). 
Qed.

Theorem neg_zero: forall wz, neg (Vzero wz) = (Vzero wz).
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  destruct x; destruct y; simpl_auto_equations.
  decEq. apply Int.neg_add_distr.
Qed.

Theorem sub_zero_r: forall x wz, 
  get_wordsize x = Some wz -> sub (Vzero wz) x = neg x.
Proof.
  destruct x; intros wz0 H; simpl_auto_equations.
Qed.

Theorem sub_add_opp: forall x wz y, 
  get_wordsize x = Some wz -> 
  sub x (Vint wz y) = add x (Vint wz (Int.neg wz y)).
Proof.
  destruct x; intros wz0 y H; simpl_auto_equations;
    rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x wz y, 
  get_wordsize x = Some wz -> 
  sub x (Vint wz (Int.neg wz y)) = add x (Vint wz y).
Proof.
  intros x wz y H.
  destruct x; simpl_auto_equations;
    rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 wz i, 
  get_wordsize v1 = Some wz -> 
  sub (add v1 (Vint wz i)) v2 = add (sub v1 v2) (Vint wz i).
Proof.
  destruct v1; destruct v2; intros wz5 i5 H; simpl_auto_equations;
    try solve [
      rewrite Int.sub_add_l; auto |
      case (zeq b b0); intro; auto; rewrite Int.sub_add_l; auto
    ].
Qed.

Theorem sub_add_r:
  forall v1 v2 wz i,
  get_wordsize v1 = Some wz -> 
  sub v1 (add v2 (Vint wz i)) = add (sub v1 v2) (Vint wz (Int.neg wz i)).
Proof.
  destruct v1; destruct v2; intros wz5 i5 H; simpl_auto_equations.
  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.

  decEq. repeat rewrite Int.sub_add_opp. 
  rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.

  case (zeq b b0); intro; simpl_auto_equations.
  decEq. 
  repeat rewrite Int.sub_add_opp.
  rewrite Int.add_assoc. decEq. decEq. decEq.
  apply Int.neg_add_distr.

  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.

  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl_auto_equations.
  decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.mul_add_distr_l.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.mul_add_distr_r.
Qed.

Theorem mul_pow2:
  forall x wz n logn,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  mul x (Vint wz n) = shl x (Vint wz logn).
Proof.
  intros x wz n logn H0 H; destruct x; simpl_auto_equations.
  rewrite (Int.is_power2_range wz _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.  

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  destruct x; destruct y; simpl_auto_equations.
  case (Int.eq wz0 i0 (Int.zero wz0)); simpl; simpl_auto_equations.
  decEq. apply Int.mods_divs.
Qed.

Theorem modu_divu:
  forall x y, modu x y = sub x (mul (divu x y) y).
Proof.
  destruct x; destruct y; simpl_auto_equations.
  generalize (Int.eq_spec wz0 i0 (Int.zero wz0));
  case (Int.eq wz0 i0 (Int.zero wz0)); simpl_auto_equations.
  intro. decEq. apply Int.modu_divu. auto.
Qed.

Theorem divs_pow2:
  forall x wz n logn,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  divs x (Vint wz n) = shrx x (Vint wz logn).
Proof.
  intros x wz n logn H0 H; destruct x; simpl_auto_equations.
  rewrite (Int.is_power2_range wz _ _ H). 
  generalize (Int.eq_spec wz n (Int.zero wz));
  case (Int.eq wz n (Int.zero wz)); intro.
  subst n. rewrite Int.is_power2_zero in H. discriminate.
  decEq. apply Int.divs_pow2. auto.
Qed.

Theorem divu_pow2:
  forall x wz n logn,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  divu x (Vint wz n) = shru x (Vint wz logn).
Proof.
  intros x wz n logn H0 H; destruct x; simpl_auto_equations.
  rewrite (Int.is_power2_range wz _ _ H). 
  generalize (Int.eq_spec wz n (Int.zero wz));
  case (Int.eq wz n (Int.zero wz)); intro.
  subst n. rewrite Int.is_power2_zero in H. discriminate.
  decEq. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x wz n logn,
  get_wordsize x = Some wz ->
  Int.is_power2 wz n = Some logn ->
  modu x (Vint wz n) = and x (Vint wz (Int.sub wz n (Int.one wz))).
Proof.
  intros x wz n logn H0 H; destruct x; simpl_auto_equations.
  generalize (Int.eq_spec wz n (Int.zero wz));
  case (Int.eq wz n (Int.zero wz)); intro.
  subst n. rewrite Int.is_power2_zero in H. discriminate.
  decEq. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl_auto_equations. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl_auto_equations. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl_auto_equations. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl_auto_equations.
  decEq. apply Int.xor_assoc.
Qed.

Theorem shl_mul: forall wz x y, 
  get_wordsize x = Some wz ->
  Val.mul x (Val.shl (Vone wz) y) = Val.shl x y.
Proof.
  intros wz x y H.
  destruct x; destruct y; simpl_auto_equations.
  case (Int.ltu wz1 i0 (Int.iwordsize wz1)); simpl_auto_equations.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  get_wordsize x = Some 31%nat ->
  Int.ltu 31 n (Int.iwordsize 31) = true ->
  shl x (Vint 31 n) = rolm x n (Int.shl 31 (Int.mone 31) n).
Proof.
  intros x n H0 H; destruct x; simpl_auto_equations.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shru_rolm:
  forall x n,
  get_wordsize x = Some 31%nat ->
  Int.ltu 31 n (Int.iwordsize 31) = true ->
  shru x (Vint 31 n) = rolm x (Int.sub 31 (Int.iwordsize 31) n) (Int.shru 31 (Int.mone 31) n).
Proof.
  intros x n H0 H; destruct x; simpl_auto_equations.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrx_carry:
  forall x y,
  add (shr x y) (shr_carry x y) = shrx x y.
Proof.
  destruct x; destruct y; simpl_auto_equations.
  case (Int.ltu wz0 i0 (Int.iwordsize wz0)); simpl_auto_equations.
  simpl. decEq. apply Int.shrx_carry.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  get_wordsize x = Some 31%nat ->
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or 31 m1 m2).
Proof.
  intros; destruct x; simpl_auto_equations.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  get_wordsize x = Some 31%nat ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu 31 (Int.add 31 n1 n2) (Int.iwordsize 31))
           (Int.and 31 (Int.rol 31 m1 n2) m2).
Proof.
  intros; destruct x; simpl_auto_equations.
  decEq. apply Int.rolm_rolm. apply int32_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m,
  get_wordsize x = Some 31%nat ->
  rolm x (Int.zero 31) m = and x (Vint 31 m).
Proof.
  intros; destruct x; simpl_auto_equations.
  decEq. apply Int.rolm_zero.
Qed.

Theorem addf_commut: forall x y, addf x y = addf y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Float.addf_commut.
Qed.

Lemma negate_cmp_mismatch:
  forall c,
  cmp_mismatch (negate_comparison c) = notbool(cmp_mismatch c).
Proof.
  destruct c; reflexivity.
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  destruct x; destruct y; simpl_auto_equations; try solve [
    rewrite Int.negate_cmp; apply notbool_negb_1 |
    case (Int.eq 31 i (Int.zero 31)); try solve [
      apply negate_cmp_mismatch | reflexivity ] |
    case (Int.eq 31 i0 (Int.zero 31)); try solve [
      apply negate_cmp_mismatch | reflexivity ] |
    case (zeq b b0); intro; try solve [
      rewrite Int.negate_cmp; apply notbool_negb_1 |
      apply negate_cmp_mismatch ]
    ].
Qed.

Theorem negate_cmpu:
  forall c x y,
  cmpu (negate_comparison c) x y = notbool (cmpu c x y).
Proof.
  destruct x; destruct y; simpl_auto_equations; try solve [
      rewrite Int.negate_cmpu; apply notbool_negb_1
    ].
    case (Int.eq 31 i (Int.zero 31)); try solve [
      apply negate_cmp_mismatch | reflexivity ].
    case (Int.eq 31 i0 (Int.zero 31)); try solve [
      apply negate_cmp_mismatch | reflexivity ].
    case (zeq b b0); intro; try solve [
      rewrite Int.negate_cmpu; apply notbool_negb_1 |
      apply negate_cmp_mismatch ].
Qed.

Lemma swap_cmp_mismatch:
  forall c, cmp_mismatch (swap_comparison c) = cmp_mismatch c.
Proof.
  destruct c; reflexivity.
Qed.
  
Theorem swap_cmp:
  forall c x y,
  cmp (swap_comparison c) x y = cmp c y x.
Proof.
  destruct x; destruct y; simpl_auto_equations; try solve [
      rewrite Int.swap_cmp; auto
    ].
  case (Int.eq 31 i (Int.zero 31)). apply swap_cmp_mismatch. auto.
  case (Int.eq 31 i0 (Int.zero 31)). apply swap_cmp_mismatch. auto.
  case (zeq b b0); intro.
    subst b0. rewrite zeq_true. rewrite Int.swap_cmp. auto.
    rewrite zeq_false. apply swap_cmp_mismatch. auto.
Qed.

Theorem swap_cmpu:
  forall c x y,
  cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  destruct x; destruct y; simpl_auto_equations; try solve [
      rewrite Int.swap_cmpu; auto
    ].
  case (Int.eq 31 i (Int.zero 31)). apply swap_cmp_mismatch. auto.
  case (Int.eq 31 i0 (Int.zero 31)). apply swap_cmp_mismatch. auto.
  case (zeq b b0); intro.
    subst b0. rewrite zeq_true. rewrite Int.swap_cmpu. auto.
    rewrite zeq_false. apply swap_cmp_mismatch. auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; simpl_auto_equations.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. 
  apply notbool_idem2.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; simpl_auto_equations.
  rewrite Float.cmp_ne_eq. rewrite notbool_negb_1. auto. 
Qed.

Lemma or_of_bool:
  forall b1 b2, or (of_bool b1) (of_bool b2) = of_bool (b1 || b2).
Proof.
  destruct b1; destruct b2; simpl_auto_equations.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl_auto_equations.
  rewrite or_of_bool. decEq. apply Float.cmp_le_lt_eq.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; simpl_auto_equations.
  rewrite or_of_bool. decEq. apply Float.cmp_ge_gt_eq.
Qed.

Definition is_bool (v: val) :=
  v = Vundef \/ v = Vtrue \/ v = Vfalse.

Lemma of_bool_is_bool:
  forall b, is_bool (of_bool b).
Proof.
  destruct b; unfold is_bool; simpl; tauto.
Qed.

Lemma undef_is_bool: is_bool Vundef.
Proof.
  unfold is_bool; tauto.
Qed.

Lemma cmp_mismatch_is_bool:
  forall c, is_bool (cmp_mismatch c).
Proof.
  destruct c; simpl; unfold is_bool; tauto.
Qed.

Lemma cmp_is_bool:
  forall c v1 v2, is_bool (cmp c v1 v2).
Proof.
  destruct v1; destruct v2; simpl_auto_equations; try apply undef_is_bool;
    try solve [apply of_bool_is_bool].
  case (Int.eq 31 i (Int.zero 31)). 
    apply cmp_mismatch_is_bool. 
    apply undef_is_bool.
  case (Int.eq 31 i0 (Int.zero 31)). 
    apply cmp_mismatch_is_bool. 
    apply undef_is_bool.
  case (zeq b b0); intro. 
    apply of_bool_is_bool. 
    apply cmp_mismatch_is_bool.
Qed.

Lemma cmpu_is_bool:
  forall c v1 v2, is_bool (cmpu c v1 v2).
Proof.
  destruct v1; destruct v2; simpl_auto_equations; try apply undef_is_bool;
    try solve [apply of_bool_is_bool].
  case (Int.eq 31 i (Int.zero 31)). 
    apply cmp_mismatch_is_bool. 
    apply undef_is_bool.
  case (Int.eq 31 i0 (Int.zero 31)). 
    apply cmp_mismatch_is_bool. 
    apply undef_is_bool.
  case (zeq b b0); intro. 
    apply of_bool_is_bool. 
    apply cmp_mismatch_is_bool.
Qed.

Lemma cmpf_is_bool:
  forall c v1 v2, is_bool (cmpf c v1 v2).
Proof.
  destruct v1; destruct v2; simpl_auto_equations;
  apply undef_is_bool || apply of_bool_is_bool.
Qed.

Lemma notbool_is_bool:
  forall v, is_bool (notbool v).
Proof.
  destruct v; simpl_auto_equations.
  apply undef_is_bool. apply of_bool_is_bool. 
  apply undef_is_bool. unfold is_bool; tauto.
  unfold is_bool. auto.
Qed.

Lemma notbool_xor:
  forall v wz, 
  get_wordsize v = Some wz ->
  is_bool v -> v = xor (notbool v) (Vone wz).
Proof.
  intros v wz H0 H. elim H; intro.
  subst v. simpl_auto_equations.
  elim H1; intro; subst v; simpl_auto_equations.
Qed.

Lemma Vundef__eq_Vbool__Vundef : forall wz, eq_Vbool wz Vundef Vundef.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; inversion J.
Qed.

Lemma Vone_not_Vzero : forall wz, Vone wz <> Vzero wz.
Proof.
  intros wz. unfold Vone. unfold Vzero.
  intro J. inversion J.
  change (1 mod Int.modulus wz) with (Int.unsigned wz (Int.one wz)) in H0.
  change (0 mod Int.modulus wz) with (Int.unsigned wz (Int.zero wz)) in H0.
  rewrite (Int.unsigned_one wz) in H0.
  rewrite (Int.unsigned_zero wz) in H0.
  inversion H0.
Qed.

Lemma Vone__eq_Vbool__Vtrue : forall wz, eq_Vbool wz (Vone wz) Vtrue.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; try solve [auto | inversion J].
    contradict J. apply Vone_not_Vzero.
Qed.

Lemma Vzero__eq_Vbool__Vfalse : forall wz, eq_Vbool wz (Vzero wz) Vfalse.
Proof.
  intros wz. unfold eq_Vbool.
  split; split; intro J; try solve [auto | inversion J].
    symmetry in J. contradict J. apply Vone_not_Vzero.
Qed.

Lemma rolm_lt_zero:
  forall v, 
  get_wordsize v = Some 31%nat ->
  eq_Vbool 31 (rolm v (Int.one 31) (Int.one 31)) 
              (cmp Clt v (Vint 31 (Int.zero 31))).
Proof.
  intros. destruct v; simpl_auto_equations; 
    try solve [apply Vundef__eq_Vbool__Vundef].

  assert (Vint 31 (Int.shru 31 i (Int.repr 31 (Z_of_nat 32 - 1))) =
          Vint 31 (Int.rolm 31 i (Int.one 31) (Int.one 31))) as EQ.
    decEq. symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite <- EQ.
  rewrite Int.shru_lt_zero. destruct (Int.lt 31 i (Int.zero 31)).
    apply Vone__eq_Vbool__Vtrue. apply Vzero__eq_Vbool__Vfalse. 
Qed.

Lemma rolm_ge_zero:
  forall v,
  get_wordsize v = Some 31%nat ->
  eq_Vbool 31 (xor (rolm v (Int.one 31) (Int.one 31)) (Vint 31 (Int.one 31))) 
              (cmp Cge v (Vint 31 (Int.zero 31))).
Proof.
  intros. destruct v; simpl_auto_equations; try solve [apply Vundef__eq_Vbool__Vundef].

  assert ((Int.shru 31 i (Int.repr 31 (Z_of_nat 32 - 1))) =
          (Int.rolm 31 i (Int.one 31) (Int.one 31))) as EQ.
    symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite <- EQ.
  rewrite Int.shru_lt_zero. destruct (Int.lt 31 i (Int.zero 31)); simpl.
    rewrite Int.xor_one_one. apply Vzero__eq_Vbool__Vfalse. 
    rewrite Int.xor_zero_one. apply Vone__eq_Vbool__Vtrue. 
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H. destruct IHlessdef_list. 
  left; congruence. tauto. tauto.
Qed.

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H. auto. destruct chunk; simpl; auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

End Val.

(** * Values and memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

Definition meminj : Type := block -> option (block * Z).

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall wz i, val_inject mi (Vint wz i) (Vint wz i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add 31 ofs1 (Int.repr 31 delta) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_inttoptr:
      forall i, val_inject mi (Vinttoptr i) (Vinttoptr i)
  | val_inject_undef: forall v,
      val_inject mi Vundef v.

Hint Resolve val_inject_int val_inject_float val_inject_ptr val_inject_inttoptr 
             val_inject_undef.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

Lemma val_load_result_inject:
  forall f chunk v1 v2,
  val_inject f v1 v2 ->
  val_inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
  intros. inv H; destruct chunk; simpl; try econstructor; eauto.
    destruct (eq_nat_dec n 31); try econstructor; eauto.
    destruct (eq_nat_dec n 31); try econstructor; eauto.
Qed.

(** Monotone evolution of a memory injection. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr. auto. Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof .
  unfold inject_incr; intros. eauto. 
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inv H0; eauto.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

(** More properties for Val. *)

Lemma add_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.add (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_add; try congruence.
    unfold Val.add_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma sub_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.sub (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_sub; try congruence.
    unfold Val.sub_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma mul_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.mul (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_mul; try congruence.
    unfold Val.mul_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. congruence.
Qed.

Lemma divu_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.divu (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_divu; try congruence.
    unfold Val.divu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma divs_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.divs (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_divs; try congruence.
    unfold Val.divs_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma modu_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.modu (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_modu; try congruence.
    unfold Val.modu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma mods_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.mods (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_mods; try congruence.
    unfold Val.mods_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.eq wz0 i1 (Int.zero wz0)); congruence.
Qed.

Lemma shl_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shl (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shl; try congruence.
    unfold Val.shl_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma shrx_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shrx (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shrx; try congruence.
    unfold Val.shrx_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma shr_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.shr (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_shr; try congruence.
    unfold Val.shr_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    destruct (Int.ltu wz0 i1 (Int.iwordsize wz0)); congruence.
Qed.

Lemma and_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.and (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_and; try congruence.
    unfold Val.and_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
Qed.

Lemma or_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.or (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_or; try congruence.
    unfold Val.or_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
Qed.

Lemma xor_isnt_ptr : forall wz i0 wz0 i1 b ofs,
  Val.xor (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_xor; try congruence.
    unfold Val.xor_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    congruence.
Qed.

Lemma cmp_isnt_ptr : forall c wz i0 wz0 i1 b ofs,
  Val.cmp c (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_cmp; try congruence.
    unfold Val.cmp_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    unfold Val.of_bool.
    destruct (Int.cmp wz0 c i0 i1).
      unfold Vtrue. unfold Vone. congruence.
      unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma cmpu_isnt_ptr : forall c wz i0 wz0 i1 b ofs,
  Val.cmpu c (Vint wz i0) (Vint wz0 i1) <> Vptr b ofs.
Proof.
  intros.
  Val.simpl_cmpu; try congruence.
    unfold Val.cmpu_obligation_1. 
    unfold DepElim.solution_left.
    unfold eq_rect_r. simpl. 
    unfold Val.of_bool.
    destruct (Int.cmpu wz0 c i0 i1).
      unfold Vtrue. unfold Vone. congruence.
      unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma val_of_bool_isnt_ptr : forall v b ofs,
  Val.of_bool v <> Vptr b ofs.
Proof.
  intros. unfold Val.of_bool. destruct v. 
    unfold Vtrue. unfold Vone. congruence.
    unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vfalse_isnt_ptr : forall b ofs,
  Vfalse <> Vptr b ofs.
Proof.
  intros. unfold Vfalse. unfold Vzero. congruence.
Qed.

Lemma Vtrue_isnt_ptr : forall b ofs,
  Vtrue <> Vptr b ofs.
Proof.
  intros. unfold Vtrue. unfold Vone. congruence.
Qed.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Proof.
  induction vs1; destruct vs2; simpl; intros; inv H; auto.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)


