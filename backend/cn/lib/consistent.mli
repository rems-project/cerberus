val function_type
  :  string ->
  Locations.t ->
  ReturnTypes.t ArgumentTypes.t ->
  unit Typing.t

val predicate : Definition.Predicate.t -> unit Typing.m

val lemma : Locations.t -> 'a -> LogicalReturnTypes.t ArgumentTypes.t -> unit Typing.t

val procedure : Locations.t -> 'TY1 Mucore.args_and_body -> unit Typing.t
