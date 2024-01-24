From Coq Require Import Arith Bool List String.
Require Import Coq.Numbers.BinNums.

Require Import CoqSymbol.
Require Import CoqLocation.
Require Import CoqIntegerType.

Import ListNotations.


Local Open Scope list_scope.

Inductive bmc_annot : Type := 
  | Abmc_id:  nat  -> bmc_annot .

Record attribute : Type := {
  attr_ns: option  CoqSymbol.identifier  ;
  attr_id: CoqSymbol.identifier ;
  attr_args: list  ((location_ocaml  * string  * list  ((location_ocaml  * string ) % type)) % type)
}.
Notation "{[ r 'with' 'attr_ns' := e ]}" := ({| attr_ns := e; attr_id := attr_id r; attr_args := attr_args r |}).
Notation "{[ r 'with' 'attr_id' := e ]}" := ({| attr_id := e; attr_ns := attr_ns r; attr_args := attr_args r |}).
Notation "{[ r 'with' 'attr_args' := e ]}" := ({| attr_args := e; attr_ns := attr_ns r; attr_id := attr_id r |}).

Inductive attributes : Type := 
  | Attrs:  list  attribute  -> attributes .

Definition no_attributes   : attributes := Attrs [].

Definition combine_attributes  (a: attributes ) (a0: attributes ) : attributes :=
  match ((a,a0)) with
  | (( Attrs xs1), ( Attrs xs2)) => Attrs ( (@ List.app _) xs1 xs2)
  end.

Definition loop_id : Set :=  nat .

(* records where a label comes from *)
Inductive label_annot : Type :=  
  | LAloop_prebody:  loop_id  -> label_annot 
  | LAloop_body:  loop_id  -> label_annot 
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
  | Aloc:  location_ocaml  -> annot  (* C source location *)
  | Auid:  string  -> annot  (* Unique ID *)
  | Amarker: nat -> annot
  | Amarker_object_types: nat -> annot
  | Abmc:  bmc_annot  -> annot 
  | Aattrs:  attributes  -> annot  (* C2X attributes *)
  | Atypedef:  CoqSymbol.sym  -> annot  (* (TODO: I don't like but hey)
                              must only be used on a ctype to indicate it is a unfolding of a typedef *)
  | Anot_explode: annot  (* tell the a-normalisation not to explode if-then-else *)
  | Alabel:  label_annot  -> annot
  | Acerb: cerb_attribute -> annot
  | Avalue: value_annot -> annot.


(*
Definition loop_attributes : Type :=  fmap  loop_id   attributes .
Definition loop_attributes_default: loop_attributes  := DAEMON.
(* [?]: removed value specification. *)

Program Fixpoint get_loc  (annots1 : list (annot ))  : option (unit ) := 
  match ( annots1) with 
    | [] =>
        None
    |( Aloc loc :: _) =>
        Some loc
    |( Astd _ :: annots') =>
        get_loc annots'
    |( Auid _ :: annots') =>
        get_loc annots'
    |( Abmc _ :: annots') =>
        get_loc annots'
    |( Aattrs _ :: annots') =>
        get_loc annots'
    |( Atypedef _ :: annots') =>
        get_loc annots'
    |( Anot_explode :: annots') =>
        get_loc annots'
    |( Alabel _ :: annots') =>
        get_loc annots'
  end.
(* [?]: removed value specification. *)

Program Fixpoint get_typedef  (annots1 : list (annot ))  : option (CoqSymbol.sym ) :=
  match ( annots1) with 
    | [] =>
        None
    |( Atypedef sym1 :: _) =>
        Some sym1
    | _ :: annots' =>
        get_typedef annots'
  end.
(* [?]: removed value specification. *)

Definition get_loc_  (annots1 : list (annot ))  : unit := 
  match ( get_loc annots1) with 
    | Some loc => loc
    | None => tt
  end.
(* [?]: removed value specification. *)

Definition only_loc  (annots1 : list (annot ))  : list (annot ):=  
  List.filter (fun (x : annot ) => match (x) with Aloc _ => true | _ => false end) annots1.
(* [?]: removed value specification. *)

Program Fixpoint get_attrs  (annots1 : list (annot ))  : option (attributes ) :=  
  match ( annots1) with 
    | [] =>
        None
    |( Aloc loc :: annots') =>
        get_attrs annots'
    |( Astd _ :: annots') =>
        get_attrs annots'
    |( Auid _ :: annots') =>
        get_attrs annots'
    |( Abmc _ :: annots') =>
        get_attrs annots'
    |( Atypedef _ :: annots') =>
        get_attrs annots'
    |( Aattrs( Attrs attributes1) :: annots') =>
       match ( get_attrs annots') with 
       | Some( Attrs attributes') => Some (Attrs ( (@ List.app _)attributes1 attributes'))
       | None => Some (Attrs attributes1)       
       end
    |( Anot_explode :: annots') =>
        get_attrs annots'
    |( Alabel _ :: annots') =>
        get_attrs annots'
  end.
(* [?]: removed value specification. *)

Definition get_attrs_  (annots1 : list (annot ))  : attributes :=  
  match ( get_attrs annots1) with 
  | Some attrs => attrs
  | None => Attrs []
  end.
(* [?]: removed value specification. *)

Program Fixpoint get_label_annot  (annots1 : list (annot ))  : option (label_annot ) :=  
  match ( annots1) with 
  | [] => None
  | Alabel la :: _ => Some la
  | _ :: annots1 => get_label_annot annots1
  end.
(* [?]: removed value specification. *)

Program Fixpoint get_uid  (annots1 : list (annot ))  : option (string ) := 
  match ( annots1) with 
    | [] =>
        None
    |( Aloc _ :: annots') =>
        get_uid annots'
    |( Astd _ :: annots') =>
        get_uid annots'
    |( Auid uid :: _) =>
        Some uid
    |( Abmc _ :: annots') =>
        get_uid annots'
    |( Atypedef _ :: annots') =>
        get_uid annots'
    |( Aattrs _ :: annots') =>
        get_uid annots'
    |( Anot_explode :: annots') =>
        get_uid annots'
    |( Alabel _ :: annots') =>
        get_uid annots'
  end.
(* [?]: removed value specification. *)

Program Fixpoint explode  (annots1 : list (annot ))  : bool := 
  match ( annots1) with 
  | Anot_explode :: _ => false
  | _ :: annots1 => explode annots1
  | [] => true
  end.
(* [?]: removed value specification. *)

Definition is_return  (annots1 : list (annot ))  : bool :=  (maybeEqualBy classical_boolean_equivalence
  (get_label_annot annots1) (Some LAreturn)).
(* [?]: removed value specification. *)

Definition is_loop_break  (annots1 : list (annot ))  : bool := 
  match ( get_label_annot annots1) with 
  | Some( LAloop_break _) => true
  | _ => false
  end.
(* [?]: removed value specification. *)

Definition set_loc  (loc : unit ) (annots1 : list (annot ))  : list (annot ):=  
  let annots' := 
    lem_list.mapMaybe (
  fun (x : annot ) => match (x) with | Aloc l => None | a => Some a end) annots1
  in
  Aloc loc :: annots'.







(* CP: not sure where best to put this *)
Inductive to_pack_unpack : Type :=  
  | TPU_Struct:  CoqSymbol.sym  -> to_pack_unpack
  | TPU_Predicate:  CoqSymbol.identifier  -> to_pack_unpack .
Definition to_pack_unpack_default: to_pack_unpack  := TPU_Struct sym_default.



*)
