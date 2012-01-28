open CoqFSetDecide
open Datatypes
open EquivDec
open FSetExtra
open FSetFacts
open FSetProperties
open FSetWeakNotin
open MinMax
open Peano_dec

type __ = Obj.t

module type ATOM = 
 sig 
  type atom = String.t
  
  val eq_atom_dec : atom -> atom -> bool
  
  val atom_fresh_for_list : atom list -> atom
 end

module AtomImpl = 
 struct 
  type atom = String.t
  
  (** val eq_atom_dec : atom -> atom -> bool **)
  
  let eq_atom_dec = fun a b -> a = b
  
  (** val nat_list_max : nat list -> nat **)
  
  let rec nat_list_max = function
    | [] -> O
    | y::l0 -> max y (nat_list_max l0)
  
  (** val atom_fresh_for_list : atom list -> atom **)
  
  let atom_fresh_for_list = Camlcoq.atom_fresh_for_list
 end

module AtomDT = 
 struct 
  type t = AtomImpl.atom
  
  (** val eq_dec : AtomImpl.atom -> AtomImpl.atom -> bool **)
  
  let eq_dec =
    AtomImpl.eq_atom_dec
 end

(** val coq_EqDec_atom : AtomImpl.atom coq_EqDec **)

let coq_EqDec_atom =
  AtomImpl.eq_atom_dec

(** val coq_EqDec_nat : nat coq_EqDec **)

let coq_EqDec_nat =
  eq_nat_dec

module AtomSetImpl = Make(AtomDT)

module AtomSetDecide = WDecide_fun(AtomDT)(AtomSetImpl)

module AtomSetNotin = Notin_fun(AtomDT)(AtomSetImpl)

module AtomSetFacts = WFacts_fun(AtomDT)(AtomSetImpl)

module AtomSetProperties = WProperties_fun(AtomDT)(AtomSetImpl)

(** val atom_fresh : AtomSetImpl.t -> AtomImpl.atom **)

let atom_fresh l =
  AtomImpl.atom_fresh_for_list (AtomSetImpl.elements l)

