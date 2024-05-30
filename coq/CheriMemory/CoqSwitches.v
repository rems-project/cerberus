From Coq.Lists Require Import List ListSet.

Import ListNotations.

Local Open Scope list_scope.

Inductive SW_pointer_arith_values := | PERMISSIVE | STRICT.

Inductive SW_PNVI_values := | PLAIN | AE | AE_UDI.

Inductive SW_revocation_values := | INSTANT | CORNUCOPIA.

Inductive cerb_switch : Set :=
| SW_pointer_arith : SW_pointer_arith_values -> cerb_switch
| SW_strict_reads : cerb_switch
| SW_forbid_nullptr_free : cerb_switch
| SW_zap_dead_pointers : cerb_switch
| SW_strict_pointer_equality : cerb_switch
| SW_strict_pointer_relationals : cerb_switch
| SW_PNVI : SW_PNVI_values -> cerb_switch
| SW_CHERI : cerb_switch
| SW_inner_arg_temps : cerb_switch
| SW_permissive_printf : cerb_switch
| SW_zero_initialised : cerb_switch
| SW_revocation: SW_revocation_values -> cerb_switch
| SW_at_magic_comments : cerb_switch.

Lemma SW_pointer_arith_values_dec: forall x y:SW_pointer_arith_values, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma SW_PNVI_values_dec: forall x y:SW_PNVI_values, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma SW_revocation_values_dec: forall x y:SW_revocation_values, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma cerb_switch_dec: forall x y:cerb_switch, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply SW_pointer_arith_values_dec.
  apply SW_PNVI_values_dec.
  apply SW_revocation_values_dec.
Qed.

Definition cerb_switches_t := set cerb_switch.

Definition has_switch (switches:cerb_switches_t) (sw : cerb_switch) : bool :=
  set_mem cerb_switch_dec sw switches.

Definition is_PNVI_switch (s:cerb_switch) :=
  match s with
   | SW_PNVI _ => true
   | _ => false
  end.

Definition has_PNVI (switches:cerb_switches_t) : bool :=
  List.existsb is_PNVI_switch switches.

Definition is_Revocation_switch (s:cerb_switch) :=
  match s with
   | SW_revocation _ => true
   | _ => false
  end.

Definition has_Revocation (switches:cerb_switches_t) : bool :=
  List.existsb is_Revocation_switch switches.

Definition is_CHERI (switches:cerb_switches_t) : bool :=
  has_switch switches (SW_CHERI).

Definition has_strict_pointer_arith (switches:cerb_switches_t) : bool :=
  has_switch switches (SW_pointer_arith STRICT).

Definition has_switch_pred (switches:cerb_switches_t) pred :=
  List.find pred switches.
