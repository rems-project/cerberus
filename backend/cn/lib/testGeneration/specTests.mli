module CF = Cerb_frontend
module A = CF.AilSyntax

val generate
  :  output_dir:string ->
  filename:string ->
  without_ownership_checking:bool ->
  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  unit

val save 
  : 
  ?perm:int ->
  string ->
  string -> 
  Pp.document ->
  unit

val compile_script
  : 
  output_dir:string ->
  test_file:string ->
  Pp.document