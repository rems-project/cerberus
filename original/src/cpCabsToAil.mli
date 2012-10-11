open CpPervasives

val desugar : string -> Cabs.file ->
  (CpSymbol.t, Position.t, Position.t) CpAil.file CpAil.result
