module MemberIndirection : sig
  val transform : GenTerms.t -> GenTerms.t
end

val normalize : unit Mucore.file -> GenDefinitions.context -> GenDefinitions.context
