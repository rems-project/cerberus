module CF = Cerb_frontend
module A = CF.AilSyntax

val generate
  :  output_dir:string ->
  filename:string ->
  CF.GenTypes.genTypeCategory A.sigma ->
  Executable_spec_extract.instrumentation list ->
  int
