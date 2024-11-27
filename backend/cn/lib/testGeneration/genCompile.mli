val compile
  :  ?ctx:GenDefinitions.context ->
  (Sym.t * ResourcePredicates.definition) list ->
  Executable_spec_extract.instrumentation list ->
  GenDefinitions.context
