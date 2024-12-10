val compile
  :  ?ctx:GenDefinitions.context ->
  (Sym.t * Definition.Predicate.t) list ->
  Executable_spec_extract.instrumentation list ->
  GenDefinitions.context
