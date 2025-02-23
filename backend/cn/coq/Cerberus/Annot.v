From Coq Require Import Arith Bool List String.
Require Import Coq.Numbers.BinNums.

Require Import Cerberus.Symbol.
Require Import Cerberus.Location.
Require Import Cerberus.IntegerType.

Import ListNotations.

Local Open Scope list_scope.

Inductive bmc_annot : Type := 
  | Abmc_id:  nat  -> bmc_annot .

Record attribute : Type := {
  attr_ns: option  Symbol.identifier  ;
  attr_id: Symbol.identifier ;
  attr_args: list  ((Location.t  * string  * list  ((Location.t  * string ) % type)) % type)
}.

Inductive attributes : Type := 
  | Attrs:  list  attribute  -> attributes .

Definition no_attributes   : attributes := Attrs [].

Definition loop_id : Set :=  nat .

(* records where a label comes from *)
Inductive label_annot : Type :=  
  | LAloop:  loop_id  -> label_annot 
  | LAloop_continue:  loop_id  -> label_annot 
  | LAloop_break:  loop_id  -> label_annot 
  | LAreturn: label_annot  (* when an Esave is annotated with this it indicates it is the
                return label *)
  | LAswitch: label_annot
  | LAcase: label_annot
  | LAdefault: label_annot.

Inductive cerb_attribute : Type :=
  | ACerb_with_address: nat -> cerb_attribute
  | ACerb_hidden: cerb_attribute.

Inductive value_annot : Type :=
| Ainteger: integerType -> value_annot.

Inductive annot : Type := 
  | Astd:  string  -> annot  (* ISO C11 Standard Annotation *)
  | Aloc:  Location.t  -> annot  (* C source location *)
  | Auid:  string  -> annot  (* Unique ID *)
  | Amarker: nat -> annot
  | Amarker_object_types: nat -> annot
  | Abmc:  bmc_annot  -> annot 
  | Aattrs:  attributes  -> annot  (* C2X attributes *)
  | Atypedef:  Symbol.sym  -> annot  (* (TODO: I don't like but hey)
                              must only be used on a ctype to indicate it is a unfolding of a typedef *)
  | Anot_explode: annot  (* tell the a-normalisation not to explode if-then-else *)
  | Alabel:  label_annot  -> annot
  | Acerb: cerb_attribute -> annot
  | Avalue: value_annot -> annot
  | Ainlined_label: Location.t -> Symbol.sym -> label_annot -> annot
  | Astmt: annot
  | Aexpr: annot.


