module CF = Cerb_frontend
module A = CF.AilSyntax

val compile_constant_tests
  :  Executable_spec_extract.instrumentation list ->
  Test.t list * Pp.document

val compile_generators
  :  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  Executable_spec_extract.instrumentation list ->
  Pp.document

val compile_generator_tests
  :  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  Executable_spec_extract.instrumentation list ->
  Test.t list * Pp.document
