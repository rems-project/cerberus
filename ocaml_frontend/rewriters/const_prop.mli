(** Pure expression rebinding elimination.

    Eliminates bindings of the form [let alias = pure(e) in body] by
    substituting [e] for [alias] throughout [body].  The binding node is
    preserved (pattern replaced by a wildcard) so that source-location
    annotations are not lost.

    Handles:
    - {b Single named bindings} ([CaseBase(Some alias, _)]) against any
      effectful RHS whose tail is [pure(e)], or [pure(sym)] (pure let).
    - {b Tuple patterns} ([CaseCtor(Ctuple, pats)]) against [Eunseq(es)]
      (effectful) or [PEctor(Ctuple, pes)] (pure), decomposed element-wise.
      Nested [Eunseq] / [PEctor(Ctuple)] structures are handled recursively.
      Extraction is partial: only elements with a known tail value are
      wildcarded; others retain their name.

    unwrap_loaded must only be set to true if the remove-unspecs
    pass/strict_reads switch has been done prior to this.

    No memory events, sequencing, or values are changed. *)

val transform_file : unwrap_loaded:bool -> unit Core.file -> unit Core.file
