open Resultat

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module Loc = Locations
module VB = VariableBinding


type binding = Sym.t * VB.t

(* type context_item = 
 *   | Binding of bindingr
 *   | Marker of Sym.t *)


type t (* = Local of context_item list *)

val empty : t

val marked : Sym.t ->  t

val concat : t -> t -> t

val get : Loc.t -> Sym.t -> t -> VB.t m

val add : binding -> t -> t

val remove : Loc.t -> Sym.t -> t -> t m

val use_resource : Loc.t -> Sym.t -> Loc.t list -> t -> t m

val since : Sym.t option -> t -> binding list * t

val is_bound : Sym.t -> t -> bool

val merge : Loc.t -> t -> t -> t m

val big_merge : Loc.t -> t -> t list -> t m

val mA : Sym.t -> (BT.t * Sym.t) -> binding
val mL : Sym.t -> LS.t -> binding
val mR : Sym.t -> RE.t -> binding
val mC : Sym.t -> LC.t -> binding
val mUR : RE.t -> binding
val mUC : LC.t -> binding

val pp : ?print_all_names:bool -> ?print_used:bool -> t -> Pp.document

val get_a : Loc.t -> Sym.t -> t -> (BT.t * Sym.t) m
val get_l : Loc.t -> Sym.t -> t -> LS.t m
val get_r : Loc.t -> Sym.t -> t -> RE.t m
val get_c : Loc.t -> Sym.t -> t -> LC.t m

val removeS : Loc.t -> Sym.t list -> t -> t m

val addA : Sym.t -> (BT.t * Sym.t) -> t -> t
val addL : Sym.t -> LS.t -> t -> t
val addR : Sym.t -> RE.t -> t -> t
val addC : Sym.t -> LC.t -> t -> t
val addUR : RE.t -> t -> t
val addUC : LC.t -> t -> t

val filter : (Sym.t -> VB.t -> 'a option) -> t -> 'a list

val all_constraints : t -> LC.t list

val filterM : (Sym.t -> VB.t -> ('a option) m) -> t -> ('a list) m

val filter_r : (Sym.t -> RE.t -> 'a option) -> t -> 'a list
val filter_rM : (Sym.t -> RE.t -> ('a option) m) -> t -> ('a list) m

val (++) : t -> t -> t







