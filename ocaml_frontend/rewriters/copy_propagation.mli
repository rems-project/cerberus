(** Pure expression rebinding elimination.

    Eliminates bindings of the form [let alias = pure(e) in body] by
    substituting [e] for [alias] throughout [body].  The binding node is
    preserved (pattern replaced by a wildcard) so that source-location
    annotations are not lost.

    Handles:
    - {b Single named bindings} ([CaseBase(Some alias, _)]) against
      [pure(sym)] (pure let) or effectful RHS whose tail is [pure(e)].
      The tail [e] may be any pure expression, not just a symbol alias.

    No memory events, sequencing, or values are changed. *)

val transform_file : unit Core.file -> unit Core.file
