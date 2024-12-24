Require Import Location.
Require Import String.
Require Import List.

(* Define the location type *)
Definition t := Location_t.

(* Define the info type *)
Definition info := (t * option string)%type.

Definition path := list t.
