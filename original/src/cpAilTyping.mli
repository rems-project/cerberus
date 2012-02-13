val annotate :
  (CpSymbol.t, Position.t, Position.t) CpAil.file CpAil.result
  -> (CpAilConstraint.t
      * ((CpSymbol.t,
         CpAilAnnotate.annotate_type,
         CpAilAnnotate.annotate_position) CpAil.file CpAil.result)) list
