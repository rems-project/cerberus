Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.
Require Import AilTypesAux.
(** definitions *)

Definition adjusted t : bool :=
  negb (array t) && negb (function t).

Definition wf_lvalue_aux q t : bool :=
  match t with
  | Pointer q' t' => implb (negb (object t')) (negb (restrict q))
  | _             => if function t
                       then unqualified q 
                       else negb (restrict q) 
  end.

Definition wf_parameters_aux wf_type :=
  fix wf_parameters p : bool :=
    match p with
    | nil         => true
    | (q, t) :: p => adjusted t && negb (incomplete t) && wf_type t && wf_lvalue_aux q t && wf_parameters p
    end.

Fixpoint wf_type t : bool :=
  let wf_parameters := wf_parameters_aux wf_type in
  match t with
  | Void
  | Basic _ => true
  | Array t _ => complete t && wf_type t
  | Function t p => negb (array  t) && negb (function t) && wf_type  t && wf_parameters p
  | Pointer q t => wf_type t && wf_lvalue_aux q t
  end.

Definition wf_lvalue q t : bool :=
  wf_type t && wf_lvalue_aux q t.

Definition wf_parameters := wf_parameters_aux wf_type.
