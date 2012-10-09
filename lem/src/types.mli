module Pfmap : Finite_map.Fmap with type k = Path.t
module TVfmap : Finite_map.Fmap with type k = Tyvar.t
module TVset : sig
  include Set.S with type elt = Tyvar.t
  val pp : Format.formatter -> t -> unit
end

type t_uvar
type t = { mutable t : t_aux }
and t_aux =
  | Tvar of Tyvar.t
  | Tfn of t * t
  | Ttup of t list
  | Tapp of t list * Path.t
  | Tuvar of t_uvar

(* Structural comparison of types, without expanding type abbreviations.
 * Probably better not to use *)
val compare : t -> t -> int

val multi_fun : t list -> t -> t
val type_subst : t TVfmap.t -> t -> t
val free_vars : t -> TVset.t

type tc_def = 
  | Tc_abbrev of Tyvar.t list * t option
  | Tc_class of Name.t list

type type_defs = tc_def Pfmap.t

(* The last Name.t list is to the module enclosing the instance declaration *)
type instance = Tyvar.t list * (Path.t * Tyvar.t) list * t * Name.t list

val head_norm : type_defs -> t -> t

val assert_equal : Ast.l -> type_defs -> t -> t -> unit

(* Gets the instance for the given class and type.  Returns None if there is
 * none.  The returned list is the set of instances that the found instance
 * relies on.  The returned Name list is to the module enclosing the instance
 * declaration *)
val get_matching_instance : type_defs -> (Path.t * t) -> instance list Pfmap.t -> (Name.t list * (Path.t * t) list) option

module type Global_defs = sig
  val d : type_defs 
  val i : (instance list) Pfmap.t 
end 

module Constraint (T : Global_defs) : sig
  val new_type : unit -> t
  val equate_types : Ast.l -> t -> t -> unit
  val add_constraint : Path.t -> t -> unit
  val add_tyvar : Tyvar.t -> unit 
  val inst_leftover_uvars : Ast.l -> TVset.t * (Path.t * Tyvar.t) list
end


val pp_type : Format.formatter -> t -> unit
val pp_class_constraint : Format.formatter -> Path.t * Tyvar.t -> unit
val pp_instance : Format.formatter -> instance -> unit
