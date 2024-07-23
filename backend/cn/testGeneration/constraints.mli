module BT = BaseTypes
module IT = IndexTerms
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type variables = (Sym.sym * (CF.Ctype.ctype * IT.t)) list

val pp_variables : variables -> Pp.document

type locations = (IT.t * Sym.sym) list

val pp_locations : locations -> Pp.document

(** Tracks indirection for a struct's member [name],
    where [carrier] carries its value of type [cty].
    **)
type member =
  { name : string; (** The name of the member *)
    carrier : Sym.sym; (** The name of the carrier*)
    cty : CF.Ctype.ctype (** The type of the member *)
  }

val pp_member : member -> Pp.document

type members = (Sym.sym * member list) list

val pp_members : members -> Pp.document

type constraints = IT.t list

val pp_constraints : constraints -> Pp.document

type goal = variables * members * locations * constraints

val pp_goal : goal -> Pp.document

(** Steps through the given [LAT.t] collecting a [goal] for our generator *)
val collect
  :  max_unfolds:int ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.mu_file ->
  (Sym.sym * CF.Ctype.ctype) list ->
  unit LAT.t ->
  goal list

val simplify : goal -> goal
