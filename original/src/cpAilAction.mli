type t
type action

val load :
  CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constant -> t
val store :
  CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constant -> t
val fn_store :
  CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constant -> t
val modify :
  CpAil.ctype -> CpAilConstraint.constant -> CpAilConstraint.constant ->
  CpAilConstraint.constant -> t
val create : CpAil.ctype -> CpAilConstraint.constant -> t
val kill : CpAilConstraint.constant -> t
val same : CpAilConstraint.constant -> CpAilConstraint.constant -> t
val id : CpAilConstraint.constant -> t
val call : unit -> t

val is_call : t -> bool
val is_access : t -> bool
val is_fn_store : t -> bool

val conflicts : (t * t) BatSet.t -> t BatSet.t -> CpAilConstraint.t

module Print : sig
  val pp_dot : (t * t) BatSet.t -> Pprint.document

  val pp_uid : t -> Pprint.document
  val pp : t -> Pprint.document
end

module Memory : sig
  val replay : CpAilConstraint.Process.p -> t list -> CpAilConstraint.t
end
