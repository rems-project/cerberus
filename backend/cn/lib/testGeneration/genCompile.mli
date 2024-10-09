val compile
  :  ?ctx:GenDefinitions.context ->
  (Sym.t * ResourcePredicates.definition) list ->
  Core_to_mucore.instrumentation list ->
  GenDefinitions.context
