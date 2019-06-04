Require Import ZArith.
Local Open Scope Z_scope.

Require Import Range.

(** definitions *)

(* defns noOverlap *)
Inductive noOverlap : range -> range -> Prop :=    (* defn noOverlap *)
 | noOverlap_Below : forall (r1 r2:range),
       max  r1   <=   min  r2   ->
     noOverlap r1 r2
 | noOverlap_Above : forall (r1 r2:range),
       max  r2   <=   min  r1   ->
     noOverlap r1 r2.
Arguments noOverlap_Below [r1 r2] _.
Arguments noOverlap_Above [r1 r2] _.

(** definitions *)

(* defns sub *)
Inductive sub : range -> range -> Prop :=    (* defn le *)
 | Sub : forall (r1 r2:range),
       max  r1   <=   max  r2   ->
       min  r2   <=   min  r1   ->
     sub r1 r2.
(** definitions *)
Arguments Sub [r1 r2] _ _.

(* defns mem *)
Inductive mem : Z -> range -> Prop :=    (* defn mem *)
 | Mem : forall (w:Z) (r:range),
      w  <=   max  r   ->
       min  r   <=  w  ->
     mem w r.
Arguments Mem [w r] _ _.

Definition memNat (n : nat) (r: range) := mem (Z_of_nat n) r. 
