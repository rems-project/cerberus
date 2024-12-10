val compile
  :  ?ctx:GenDefinitions.context ->
  (Sym.t * ResourcePredicates.Definition.t) list ->
  Executable_spec_extract.instrumentation list ->
  GenDefinitions.context
