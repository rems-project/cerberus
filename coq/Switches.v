Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.

Import ListNotations.

Local Open Scope list_scope.

Inductive SW_pointer_arith_values := | PERMISSIVE | STRICT.


Inductive SW_PNVI_values := | PLAIN | AE | AE_UDI.

Inductive cerb_switch : Set :=
| SW_pointer_arith : SW_pointer_arith_values -> cerb_switch
| SW_strict_reads : cerb_switch
| SW_forbid_nullptr_free : cerb_switch
| SW_zap_dead_pointers : cerb_switch
| SW_strict_pointer_equality : cerb_switch
| SW_strict_pointer_relationals : cerb_switch
| SW_PNVI : SW_PNVI_values -> cerb_switch
| SW_CHERI : cerb_switch.

Lemma SW_pointer_arith_values_dec: forall x y:SW_pointer_arith_values, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma SW_PNVI_values_dec: forall x y:SW_PNVI_values, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma cerb_switch_dec: forall x y:cerb_switch, {x = y} + {x <> y}.
Proof.
  decide equality.
  apply SW_pointer_arith_values_dec.
  apply SW_PNVI_values_dec.
Qed.

Definition default_switches: set cerb_switch :=
  [
    SW_CHERI;
    SW_PNVI AE_UDI;
    SW_strict_pointer_equality;
    SW_strict_pointer_relationals;
    SW_pointer_arith STRICT;
    SW_strict_reads
  ].

Definition get_switches (_ : unit) := default_switches.

Definition has_switch (sw : cerb_switch) : bool :=
  set_mem cerb_switch_dec sw default_switches.

Definition is_PNVI (_ : unit) : bool :=
  List.existsb
    (fun (s : cerb_switch) =>
      match s with
      | SW_PNVI _ => true
      | _ => false
      end) default_switches.

Definition is_CHERI (_ : unit) : bool :=
  has_switch (SW_CHERI).

Definition has_strict_pointer_arith (_ : unit) : bool :=
  has_switch (SW_pointer_arith STRICT).
