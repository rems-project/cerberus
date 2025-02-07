Require Import Location.
Require Import String.
Require Import List.

(* TODO: maybe this level of indirection is not needed. Keeping it for now to mirror OCaml code *)
Definition t := Location.t.

(* Define the info type *)
Definition info := (t * option string)%type.

Definition path := list t.
