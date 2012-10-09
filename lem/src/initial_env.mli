open Types
type t = 
    ((type_defs * instance list Pfmap.t) * Typed_ast.env) *
    (Typed_ast.target option * Ulib.Text.t list) list
val add_to_init : Typed_ast.target -> string -> t -> t

module Initial_libs(P : sig val path : string end) : sig
  val init : t
end
