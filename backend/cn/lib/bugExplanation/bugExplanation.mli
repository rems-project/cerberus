module CF = Cerb_frontend
module A = CF.AilSyntax

val synthesize_replicators
  :  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  Executable_spec_extract.instrumentation list ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list

val synthesize_shape_analyzers
  :  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  Executable_spec_extract.instrumentation list ->
  (A.sigma_declaration * CF.GenTypes.genTypeCategory A.sigma_function_definition) list
